// 8086tiny: a tiny, highly functional, highly portable PC emulator/VM
// Copyright 2013-14, Adrian Cable (adrian.cable@gmail.com) - http://www.megalith.co.uk/8086tiny
//
// Revision 1.25
//
// This work is licensed under the MIT License. See included LICENSE.TXT.
#include <stdio.h>

#include <time.h>
#include <sys/timeb.h>
#include <memory.h>

#include <unistd.h>
#include <fcntl.h>

#include <stdint.h>

#include "regs8086.h"

// Emulator system constants
#define IO_PORT_COUNT 0x10000
#define RAM_SIZE 0x10FFF0
#define REGS_BASE 0xF0000
#define VIDEO_RAM_SIZE 0x10000

// Graphics/timer/keyboard update delays (explained later)
#ifndef GRAPHICS_UPDATE_DELAY
#define GRAPHICS_UPDATE_DELAY 360000
#endif
#define KEYBOARD_TIMER_UPDATE_DELAY 20000

// Lookup tables in the BIOS binary
#define TABLE_XLAT_OPCODE 8
#define TABLE_XLAT_SUBFUNCTION 9
#define TABLE_STD_FLAGS 10
#define TABLE_PARITY_FLAG 11
#define TABLE_BASE_INST_SIZE 12
#define TABLE_I_W_SIZE 13
#define TABLE_I_MOD_SIZE 14
#define TABLE_COND_JUMP_DECODE_A 15
#define TABLE_COND_JUMP_DECODE_B 16
#define TABLE_COND_JUMP_DECODE_C 17
#define TABLE_COND_JUMP_DECODE_D 18
#define TABLE_FLAGS_BITFIELDS 19

// Bitfields for TABLE_STD_FLAGS values
#define FLAGS_UPDATE_SZP 1
#define FLAGS_UPDATE_AO_ARITH 2
#define FLAGS_UPDATE_OC_LOGIC 4

// Helper macros

// Decode mod, r_m and reg fields in instruction
#define DECODE_RM_REG scratch2_uint = 4 * !i_mod, \
					  op_to_addr = rm_addr = i_mod < 3 ? SEGREG(seg_override_en ? seg_override : bios_table_lookup[scratch2_uint + 3][i_rm], bios_table_lookup[scratch2_uint][i_rm], regs16[bios_table_lookup[scratch2_uint + 1][i_rm]] + bios_table_lookup[scratch2_uint + 2][i_rm] * i_data1+) : GET_REG_ADDR(i_rm), \
					  op_from_addr = GET_REG_ADDR(i_reg), \
					  i_d && (scratch_uint = op_from_addr, op_from_addr = rm_addr, op_to_addr = scratch_uint)

// Return memory-mapped register location (offset into mem array) for register #reg_id
#define GET_REG_ADDR(reg_id) (REGS_BASE + (i_w ? 2 * reg_id : 2 * reg_id + reg_id / 4 & 7))

// Returns number of top bit in operand (i.e. 8 for 8-bit operands, 16 for 16-bit operands)
#define TOP_BIT 8*(i_w + 1)

// Opcode execution unit helpers
#define OPCODE ;break; case
#define OPCODE_CHAIN ; case

static uint8_t xlat_opcode_id;
static uint8_t bios_table_lookup[20][256];
static uint8_t raw_opcode_id;
static uint8_t extra;
static uint8_t i_mod_size;

static unsigned set_flags_type;

// Convert raw opcode to translated opcode index. This condenses a large number of different encodings of similar
// instructions into a much smaller number of distinct functions, which we then execute
static void set_opcode(unsigned char opcode) {
	xlat_opcode_id = bios_table_lookup[TABLE_XLAT_OPCODE][raw_opcode_id = opcode];
	extra = bios_table_lookup[TABLE_XLAT_SUBFUNCTION][opcode];
	i_mod_size = bios_table_lookup[TABLE_I_MOD_SIZE][opcode];
	set_flags_type = bios_table_lookup[TABLE_STD_FLAGS][opcode];
}

// [I]MUL/[I]DIV/DAA/DAS/ADC/SBB helpers
#define MUL_MACRO(op_data_type,out_regs) (set_opcode(0x10), \
										  out_regs[i_w + 1] = (op_result = CAST(op_data_type)mem[rm_addr] * (op_data_type)*out_regs) >> 16, \
										  regs16[REG_AX] = op_result, \
										  set_OF(set_CF(op_result - (op_data_type)op_result)))
#define DIV_MACRO(out_data_type,in_data_type,out_regs) (scratch_int = CAST(out_data_type)mem[rm_addr]) && !(scratch2_uint = (in_data_type)(scratch_uint = (out_regs[i_w+1] << 16) + regs16[REG_AX]) / scratch_int, scratch2_uint - (out_data_type)scratch2_uint) ? out_regs[i_w+1] = scratch_uint - scratch_int * (*out_regs = scratch2_uint) : pc_interrupt(0)
#define DAA_DAS(op1,op2,mask,min) set_AF((((scratch2_uint = regs8[REG_AL]) & 0x0F) > 9) || regs8[FLAG_AF]) && (op_result = regs8[REG_AL] op1 6, set_CF(regs8[FLAG_CF] || (regs8[REG_AL] op2 scratch2_uint))), \
								  set_CF((((mask & 1 ? scratch2_uint : regs8[REG_AL]) & mask) > min) || regs8[FLAG_CF]) && (op_result = regs8[REG_AL] op1 0x60)
#define ADC_SBB_MACRO(a) OP(a##= regs8[FLAG_CF] +), \
						 set_CF(regs8[FLAG_CF] && (op_result == op_dest) || (a op_result < a(int)op_dest)), \
						 set_AF_OF_arith()

// Execute arithmetic/logic operations in emulator memory/registers
#define R_M_OP(dest,op,src) (i_w ? op_dest = CAST(unsigned short)dest, op_result = CAST(unsigned short)dest op (op_source = CAST(unsigned short)src) \
								 : (op_dest = dest, op_result = dest op (op_source = CAST(unsigned char)src)))
#define MEM_OP(dest,op,src) R_M_OP(mem[dest],op,mem[src])
#define OP(op) MEM_OP(op_to_addr,op,op_from_addr)

// Increment or decrement a register #reg_id (usually SI or DI), depending on direction flag and operand size (given by i_w)
#define INDEX_INC(reg_id) (regs16[reg_id] -= (2 * regs8[FLAG_DF] - 1)*(i_w + 1))

// Helpers for stack operations
#define R_M_PUSH(a) (i_w = 1, R_M_OP(mem[SEGREG(REG_SS, REG_SP, --)], =, a))
#define R_M_POP(a) (i_w = 1, regs16[REG_SP] += 2, R_M_OP(a, =, mem[SEGREG(REG_SS, REG_SP, -2+)]))

// Convert segment:offset to linear address in emulator memory space
#define SEGREG(reg_seg,reg_ofs,op) 16 * regs16[reg_seg] + (unsigned short)(op regs16[reg_ofs])

// Returns sign bit of an 8-bit or 16-bit operand
#define SIGN_OF(a) (1 & (i_w ? CAST(short)a : a) >> (TOP_BIT - 1))

// Reinterpretation cast
#define CAST(a) *(a*)&

// Global variable definitions
static uint8_t mem[RAM_SIZE], io_ports[IO_PORT_COUNT], *opcode_stream, *regs8, i_rm, i_w, i_reg, i_mod, i_d, i_reg4bit, rep_mode, seg_override_en, rep_override_en, trap_flag, int8_asap, scratch_uchar, io_hi_lo, *vid_mem_base, spkr_en, bios_table_lookup[20][256];
uint16_t *regs16, reg_ip, seg_override, file_index, wave_counter;
unsigned int op_source, op_dest, rm_addr, op_to_addr, op_from_addr, i_data0, i_data1, i_data2, scratch_uint, scratch2_uint, inst_counter, GRAPHICS_X, GRAPHICS_Y, pixel_colors[16], vmem_ctr;
int op_result, disk[3], scratch_int;
time_t clock_buf;
struct timeb ms_clock;

// Helper functions

// Set carry flag
static char set_CF(int new_CF)
{
	return regs8[FLAG_CF] = !!new_CF;
}

// Set auxiliary flag
static char set_AF(int new_AF)
{
	return regs8[FLAG_AF] = !!new_AF;
}

// Set overflow flag
static char set_OF(int new_OF)
{
	return regs8[FLAG_OF] = !!new_OF;
}

// Set auxiliary and overflow flag after arithmetic operations
static char set_AF_OF_arith()
{
	set_AF((op_source ^= op_dest ^ op_result) & 0x10);
	if (op_result == op_dest)
		return set_OF(0);
	else
		return set_OF(1 & (regs8[FLAG_CF] ^ op_source >> (TOP_BIT - 1)));
}

// Assemble and return emulated CPU FLAGS register in scratch_uint
void make_flags()
{
	scratch_uint = 0xF002; // 8086 has reserved and unused flags set to 1
	for (int i = 9; i--;)
		scratch_uint += regs8[FLAG_CF + i] << bios_table_lookup[TABLE_FLAGS_BITFIELDS][i];
}

// Set emulated CPU FLAGS register from regs8[FLAG_xx] values
void set_flags(int new_flags)
{
	for (int i = 9; i--;)
		regs8[FLAG_CF + i] = !!(1 << bios_table_lookup[TABLE_FLAGS_BITFIELDS][i] & new_flags);
}

static void memww(uint8_t *mem, uint16_t w) {
	mem[0] = w;
	mem[1] = w >> 8;
}

static void memw16le(uint16_t *mem, uint16_t val) {
	memww((uint8_t *) mem, val);
}

// read a memory word from byte memory
static uint16_t memrw(uint8_t *mem) {
	const uint16_t vl = mem[0];
	const uint16_t vh = mem[1];

	return (vh << 8) | vl;
}

// read a memory word from word memory
static uint16_t memr16le(uint16_t *mem) {
	return memrw((uint8_t *) mem);
}

static void memw32le(uint32_t *mem, uint32_t val) {
	uint8_t *mem8 = (uint8_t *) mem;

	mem8[0] = val;
	mem8[1] = (val >> 8);
	mem8[2] = (val >> 16);
	mem8[3] = (val >> 24);
}

// Execute INT #interrupt_num on the emulated machine
char pc_interrupt(unsigned char interrupt_num)
{
	uint16_t val;
	set_opcode(0xCD); // Decode like INT

	make_flags();
	R_M_PUSH(scratch_uint);
	val = memr16le(regs16 + REG_CS);
	R_M_PUSH(val);
	R_M_PUSH(reg_ip);
	MEM_OP(REGS_BASE + 2 * REG_CS, =, 4 * interrupt_num + 2);
	R_M_OP(reg_ip, =, mem[4 * interrupt_num]);

	return regs8[FLAG_TF] = regs8[FLAG_IF] = 0;
}

// AAA and AAS instructions - which_operation is +1 for AAA, and -1 for AAS
int AAA_AAS(char which_operation)
{
	return (regs16[REG_AX] += 262 * which_operation*set_AF(set_CF(((regs8[REG_AL] & 0x0F) > 9) || regs8[FLAG_AF])), regs8[REG_AL] &= 0x0F);
}

/* return 20 bit linear address */
static uint32_t linear(uint16_t seg, uint16_t ofs) {
	const uint32_t sr = seg;
	const uint32_t so = ofs;

	return (sr << 4) + so;
}

static const char *reg16name(uint8_t reg) {
	const char *regs[] = { "AX", "CX", "DX", "BX", "SP", "BP", "SI", "DI" };

	return regs[reg&7];
}

static const char *reg8name(uint8_t reg) {
	const char *regs[] = { "AL", "AH", "CL", "CH", "DL", "DH", "BL", "BH" };

	return regs[reg&7];
}

static const char *sregname(uint8_t reg) {
	const char *regs[] = { "ES", "CS", "SS", "DS" };

	return regs[reg&3];
}

static unsigned parity(uint8_t val) {
	unsigned i;
	unsigned p = 1;

	for (i = 0; i < 8; i++) {
		if (val & 1) {
			p = !p;
		}
		val = val >> 1;
	}

	return p;
}

static void update_flags16(uint16_t result, unsigned carry, unsigned aux, unsigned overflow) {
	regs8[FLAG_SF] = !!(result & 0x8000);
	regs8[FLAG_ZF] = result == 0;
	regs8[FLAG_PF] = parity(result);
	regs8[FLAG_CF] = carry;
	regs8[FLAG_AF] = aux;
	regs8[FLAG_OF] = overflow;
}

static void add_update_flags8(uint8_t cmp, uint8_t val) {
	const uint8_t result = cmp + val;

	regs8[FLAG_SF] = !!(result & 0x80);
	regs8[FLAG_ZF] = result == 0;
	regs8[FLAG_PF] = parity(result);
	regs8[FLAG_CF] = (cmp & 0x80) && (val & 0x80);
	regs8[FLAG_AF] = 0;	// FIXME: how to compute?
	regs8[FLAG_OF] = 0;	// FIXME: how to compute?
}

static void add_update_flags16(uint16_t cmp, uint16_t val) {
	const uint16_t result = cmp + val;

	regs8[FLAG_SF] = result & 0x8000;
	regs8[FLAG_ZF] = result == 0;
	regs8[FLAG_PF] = parity(result);
	regs8[FLAG_CF] = (cmp & 0x8000) && (val & 0x8000);
	regs8[FLAG_AF] = 0;	// FIXME: how to compute?
	regs8[FLAG_OF] = 0;	// FIXME: how to compute?
}

static uint16_t direct_addr(uint8_t *pmem) {
	uint16_t addr = pmem[1];

	addr <<= 8;
	addr |= pmem[0];

	return addr;
}

static uint16_t sign_extend(uint8_t v) {
	return (int16_t) (int8_t) v;
}

static void cmpw(uint16_t v1, uint16_t v2) {
	const uint16_t mv2 = -v2;

	add_update_flags16(v1, mv2);
}

static void cmpb(uint8_t v1, uint8_t v2) {
	const uint8_t mv2 = -v2;

	add_update_flags8(v1, mv2);
}

// jump conditional byte
static uint16_t jcb(unsigned cond, uint8_t disp) {
	return (cond) ? sign_extend(disp) + 2 : 2;
}

static void stos(const uint8_t w) {
	uint16_t       di = memr16le(regs16 + REG_DI);
	const uint16_t es = memr16le(regs16 + REG_ES);
	uint16_t      dii = 0;

	if (w) {
		const uint16_t val = memr16le(regs16 + REG_AX);

		mem[linear(es, di)] = val & 0xff;
		mem[linear(es, di + 1)] = val >> 8;
		dii = 2;
	} else {
		mem[linear(es, di)] = regs8[REG_AL];
		dii = 1;
	}

	if (regs8[FLAG_DF]) {
		di -= dii;
	} else {
		di += dii;
	}
	memw16le(regs16 + REG_DI, di);
}

static void movs(const uint8_t w, unsigned segment_prefix, unsigned segment) {
	uint16_t       di   = memr16le(regs16 + REG_DI);
	uint16_t       si   = memr16le(regs16 + REG_SI);
	const uint16_t es   = memr16le(regs16 + REG_ES);
	const uint16_t segn = (segment_prefix) ? segment : 3;
	const uint16_t seg  = memr16le(regs16 + REG_ES + segn);
	uint16_t      dii = 0;

	if (w) {
		const uint16_t val = memrw(mem + linear(seg, si));

		memww(mem + linear(es, di), val);
		dii = 2;
	} else {
		mem[linear(es, di)] = mem[linear(seg, si)];
		dii = 1;
	}

	if (regs8[FLAG_DF]) {
		di -= dii;
		si -= dii;
	} else {
		di += dii;
		si += dii;
	}
	memw16le(regs16 + REG_DI, di);
	memw16le(regs16 + REG_SI, si);
}

static void push16(uint16_t val) {
	const uint16_t sp = memr16le(regs16 + REG_SP);
	const uint16_t ss = memr16le(regs16 + REG_SS);

	memww(mem + linear(ss, sp - 2), val);
	memw16le(regs16 + REG_SP, sp - 2);
}

static void pushf(void) {
	const uint16_t cf = regs8[FLAG_CF];
	const uint16_t pf = regs8[FLAG_PF];
	const uint16_t af = regs8[FLAG_AF];
	const uint16_t zf = regs8[FLAG_ZF];
	const uint16_t sf = regs8[FLAG_SF];
	const uint16_t tf = regs8[FLAG_TF];
	const uint16_t ff = regs8[FLAG_IF];
	const uint16_t df = regs8[FLAG_DF];
	const uint16_t of = regs8[FLAG_OF];
	const uint16_t flags =
		cf | (pf << 2) | (af << 4) | (zf << 6) |
		(sf << 7) | (tf << 8) | (ff << 9) |
		(df << 10) | (of << 11);

	push16(flags);
}

static uint16_t intr(const uint8_t v, const uint16_t pc, const uint16_t addr) {
	const uint16_t cs = memr16le(regs16 + REG_CS);

	pushf();
	regs8[FLAG_IF] = 0;
	regs8[FLAG_TF] = 0;
	push16(cs);
	memw16le(regs16 + REG_CS, memrw(mem + addr + 2));
	push16(pc + (v) ? 2 : 1);

	return memrw(mem + addr);
}

static uint16_t decode(uint8_t *mem, uint16_t pc) {
	uint8_t   *regs8  = mem + REGS_BASE;
	uint16_t  *regs16 = (uint16_t *) regs8;
	const uint16_t sp = memr16le(regs16 + REG_SP);
	const uint16_t bp = memr16le(regs16 + REG_BP);
	const uint16_t si = memr16le(regs16 + REG_SI);
	const uint16_t di = memr16le(regs16 + REG_DI);
	const uint16_t cs = memr16le(regs16 + REG_CS);
	const uint16_t ds = memr16le(regs16 + REG_DS);
	const uint16_t ss = memr16le(regs16 + REG_SS);
	const uint16_t es = memr16le(regs16 + REG_ES);
	uint8_t     *pmem = mem + linear(cs, pc);
	unsigned segment_prefix = 0;
	unsigned segment = 0;			// offset from 0, + REG_ES for register number
	unsigned lock_prefix = 0;
	unsigned repeat_prefix = 0;
	unsigned repeat_zero = 0;

	printf("    O D I T S Z A P C\n");
	printf("PSW %1x %1x %1x %1x %1x %1x %1x %1x %1x\n\n",
		regs8[FLAG_OF], regs8[FLAG_DF], regs8[FLAG_IF], regs8[FLAG_TF],
		regs8[FLAG_SF], regs8[FLAG_ZF], regs8[FLAG_AF], regs8[FLAG_PF],
		regs8[FLAG_CF]);
	printf(" AX  %02x %02x        PMem\n", regs8[REG_AH], regs8[REG_AL]);
	printf(" BX  %02x %02x        %02x\n", regs8[REG_BH], regs8[REG_BL], pmem[0]);
	printf(" CX  %02x %02x        %02x\n", regs8[REG_CH], regs8[REG_CL], pmem[1]);
	printf(" DX  %02x %02x        %02x\n", regs8[REG_DH], regs8[REG_DL], pmem[2]);
	printf(" SP  %02x %02x        %02x\n", sp >> 8, sp & 0xff, pmem[3]);
	printf(" BP  %02x %02x        %02x\n", bp >> 8, bp & 0xff, pmem[4]);
	printf(" SI  %02x %02x        %02x\n", si >> 8, si & 0xff, pmem[5]);
	printf(" DI  %02x %02x        %02x\n", di >> 8, di & 0xff, pmem[6]);
	printf(" PC  %02x %02x\n", pc >> 8, pc & 0xff);
	printf(" CS  %02x %02x\n", cs >> 8, cs & 0xff);
	printf(" DS  %02x %02x\n", ds >> 8, ds & 0xff);
	printf(" SS  %02x %02x\n", ss >> 8, ss & 0xff);
	printf(" ES  %02x %02x        ", es >> 8, es & 0xff);

prefix:
	pmem = mem + linear(cs, pc);
	if (pmem[0] == 0xeb) {
		const int16_t offset = (int16_t) ((int8_t) pmem[1]);

		pc = pc + (uint16_t) offset + 2;
		printf("JMP %02x", pmem[1]);
	} else if ((pmem[0] & (~0xf)) == 0xb0) {
		const uint8_t w = (pmem[0] >> 3) & 1;
		const uint8_t r = pmem[0] & 7;

		if (w) {
			const uint16_t val = ((uint16_t) pmem[2] << 8) + pmem[1];

			memw16le(regs16 + r, val);
			printf("MOV %s, %04x", reg16name(r), val);
		} else {
			uint8_t map[] = {
				REG_AL, REG_CL, REG_DL, REG_BL, REG_AH, REG_CH, REG_DH, REG_BH };

			regs8[map[r]] = pmem[1];
			printf("MOV %s, %02x", reg8name(map[r]), pmem[1]);
		}

		pc = pc + 2 + w;
	} else if (pmem[0] == 0x8e) {
		const uint8_t mod = pmem[1] >> 6;
		const uint8_t reg = (pmem[1] >> 3) & 7;
		const uint8_t rm  = pmem[1] & 7;

		if (mod == 3) {
			uint16_t *dest = NULL;

			// FIXME: validate reg (000, 010, 011 are valid)
			printf("MOV %s, %s", sregname(reg), reg16name(rm));
			memw16le(regs16 + REG_ES + reg, memr16le(regs16 + rm));
		}

		pc = pc + 2;
	} else if ((pmem[0] & (~3)) == 0x88) {
		const uint8_t  d    = (pmem[0] >> 1) & 1;
		const uint8_t  w    = pmem[0] & 1;
		const uint8_t  mod  = pmem[1] >> 6;
		const uint8_t  reg  = (pmem[1] >> 3) & 7;
		const uint8_t  rm   = pmem[1] & 7;
		const uint16_t segn = (segment_prefix) ? segment : 3;
		const uint16_t seg  = memr16le(regs16 + REG_ES + segn);
		const uint8_t map[] = {
			REG_AL, REG_CL, REG_DL, REG_BL, REG_AH, REG_CH, REG_DH, REG_BH };

		uint16_t pci = 2;

		if (mod == 0) {
			if (rm == 6) {
				const uint16_t addr = direct_addr(pmem + 2);

				if (d) {
					if (w) {
						const uint16_t val = memrw(mem + linear(seg, addr));

						memw16le(regs16 + reg, memrw(mem + linear(seg, addr)));
						printf("MOV %s, [%s:%04x]", reg16name(reg), sregname(segn), addr);
					} else {
						regs8[map[reg]] = mem[linear(seg, addr)];
						printf("MOV %s, [%s:%04x]", reg8name(map[reg]), sregname(segn), addr);
					}
				} else {
					if (w) {
						const uint16_t val = memr16le(regs16 + reg);

						memww(mem + linear(seg, addr), val);

						printf("MOV [%s:%04x], %s", sregname(segn), addr, reg16name(reg));
					} else {
						mem[linear(seg, addr)] = regs8[map[reg]];
						printf("MOV [%s:%04x], %s", sregname(segn), addr, reg8name(map[reg]));
					}
					// dst memory
				}
				pci = 4;
			}
		} else if (mod == 3) {
			if (d) {
			} else {
				if (w) {
					memw16le(regs16 + rm, memr16le(regs16 + reg));
					printf("MOV %s, %s", reg16name(rm), reg16name(reg));
				} else {
					regs8[map[rm]] = regs8[map[reg]];
					printf("MOV %s, %s", reg8name(map[rm]), reg8name(map[reg]));
				}
				pci = 2;
			}
		}

		pc = pc + pci;
	} else if ((pmem[0] & (~1)) == 0xc6) {
		const uint8_t  w    = pmem[0] & 1;
		const uint8_t  mod  = pmem[1] >> 6;
		const uint8_t  reg  = (pmem[1] >> 3) & 7;
		const uint8_t  rm   = pmem[1] & 7;
		const uint16_t segn = (segment_prefix) ? segment : 3;
		const uint16_t seg  = memr16le(regs16 + REG_ES + segn);
		uint16_t pci = 0;

		if (mod == 0) {
			if (rm == 6) {
				const uint16_t addr = direct_addr(pmem + 2);

				if (w) {
					const uint16_t val = memrw(pmem + 4);

					printf("MOV WORD [%s:%04x], %04x", sregname(segn), addr, val);
					pci = 6;
				} else {
					mem[linear(seg, addr)] = pmem[4];
					printf("MOV BYTE [%s:%04x], %02x", sregname(segn), addr, pmem[4]);
					pci = 5;
				}
			} else {
			}
		} else {
		}

		pc = pc + pci;
	} else if ((pmem[0] & (~1)) == 0xa0) {
		const uint8_t  w    = pmem[0] & 1;
		const uint16_t segn = (segment_prefix) ? segment : 3;
		const uint16_t seg  = memr16le(regs16 + REG_ES + segn);
		const uint16_t addr = memrw(pmem + 1);

		if (w) {
			const uint16_t val = memr16le(regs16 + REG_AX);

			memww(mem + linear(seg, addr), val);
			printf("MOV AX, [%s:%04x]", sregname(segn), addr);
		} else {
			regs8[REG_AL] = mem[linear(seg, addr)];
			printf("MOV AL, [%s:%04x]", sregname(segn), addr);
		}
		pc = pc + 3;
	} else if ((pmem[0] & (~1)) == 0xa2) {
		const uint8_t  w    = pmem[0] & 1;
		const uint16_t segn = (segment_prefix) ? segment : 3;
		const uint16_t seg  = memr16le(regs16 + REG_ES + segn);
		const uint16_t addr = memrw(pmem + 1);

		if (w) {
			const uint16_t val = memr16le(regs16 + REG_AX);

			memww(mem + linear(seg, addr), val);
			printf("MOV [%s:%04x], AX", sregname(segn), addr);
		} else {
			mem[linear(seg, addr)] = regs8[REG_AL];
			printf("MOV [%s:%04x], AL", sregname(segn), addr);
		}
		pc = pc + 3;
	} else if ((pmem[0] & (~1)) == 0xa4) {
		const uint8_t w = pmem[0] & 1;

		if (repeat_prefix) {
			uint16_t cx = memr16le(regs16 + REG_CX);

			while (cx) {
				movs(w, segment_prefix, segment);
				cx--;
				memw16le(regs16 + REG_CX, cx);
			}

			printf("REP MOVS%c", (w) ? 'W' : 'B');
		} else {
			movs(w, segment_prefix, segment);
			printf("MOVS%c", (w) ? 'W' : 'B');
		}

		pc++;
	} else if ((pmem[0] & (~0x18)) == 0x06) {
		const uint8_t sreg = (pmem[0] >> 3) & 3;
		const uint16_t val = memr16le(regs16 + REG_ES + sreg);
		const uint16_t sp  = memr16le(regs16 + REG_SP);
		const uint16_t ss  = memr16le(regs16 + REG_SS);

		memw16le(regs16 + REG_SP, sp - 1);
		mem[linear(ss, sp - 1)] = val >> 8;
		memw16le(regs16 + REG_SP, sp - 2);
		mem[linear(ss, sp - 2)] = val;

		printf("PUSH %s", sregname(sreg));

		pc = pc + 1;
	} else if (pmem[0] == 0x0f) {
		if (pmem[1] == 0x01) {
			time_t       clock_buf;
			struct timeb ms_clock;
			const uint16_t es = memr16le(regs16 + REG_ES);
			const uint16_t bx = memr16le(regs16 + REG_BX);

			time(&clock_buf);
			ftime(&ms_clock);
			memcpy(mem + linear(es, bx), localtime(&clock_buf), sizeof(struct tm));
			memww(mem + linear(es, bx + 36), ms_clock.millitm);

			printf("SYS RTC");
		}
		pc = pc + 2;
	} else if ((pmem[0] & (~0x18)) == 0x07) {
		const uint8_t sreg = (pmem[0] >> 3) & 3;
		const uint16_t sp  = memr16le(regs16 + REG_SP);
		const uint16_t ss  = memr16le(regs16 + REG_SS);
		uint8_t *sr        = (uint8_t *) (regs16 + REG_ES + sreg);

		sr[0] = mem[linear(ss, sp)];
		memw16le(regs16 + REG_SP, sp + 1);
		sr[1] = mem[linear(ss, sp + 1)];
		memw16le(regs16 + REG_SP, sp + 2);

		printf("POP %s", sregname(sreg));

		pc = pc + 1;
	} else if (pmem[0] == 0x9d) {
		const uint16_t sp = memr16le(regs16 + REG_SP);
		const uint16_t ss = memr16le(regs16 + REG_SS);
		const uint16_t vl = mem[linear(ss, sp)];
		const uint16_t vh = mem[linear(ss, sp + 1)];

		regs8[FLAG_CF] = vl & 1;
		regs8[FLAG_PF] = !!(vl & 4);
		regs8[FLAG_AF] = !!(vl & 0x10);
		regs8[FLAG_ZF] = !!(vl & 0x40);
		regs8[FLAG_SF] = !!(vl & 0x80);

		regs8[FLAG_TF] = vh & 1;
		regs8[FLAG_IF] = !!(vh & 2);
		regs8[FLAG_DF] = !!(vh & 4);
		regs8[FLAG_OF] = !!(vh & 8);
		memw16le(regs16 + REG_SP, sp + 2);

		printf("POPF");
		pc++;
	} else if ((pmem[0] & (~7)) == 0x58) {
		const uint8_t  reg = pmem[0] & 7;
		const uint16_t sp  = memr16le(regs16 + REG_SP);
		const uint16_t ss  = memr16le(regs16 + REG_SS);
		const uint16_t vl  = mem[linear(ss, sp)];
		const uint16_t vh  = mem[linear(ss, sp + 1)];

		memw16le(regs16 + reg, (vh << 8) | vl);
		memw16le(regs16 + REG_SP, sp + 2);
		printf("POP %s", reg16name(reg));
		pc++;
	} else if ((pmem[0] & (~7)) == 0x50) {
		const uint8_t reg  = pmem[0] & 7;
		const uint16_t val = memr16le(regs16 + reg);
		const uint16_t sp  = memr16le(regs16 + REG_SP);
		const uint16_t ss  = memr16le(regs16 + REG_SS);

		memw16le(regs16 + REG_SP, sp - 1);
		mem[linear(ss, sp - 1)] = val >> 8;
		memw16le(regs16 + REG_SP, sp - 2);
		mem[linear(ss, sp - 2)] = val;

		printf("PUSH %s", reg16name(reg));

		pc = pc + 1;
	} else if (pmem[0] == 0xfc) {
		regs8[FLAG_DF] = 0;
		printf("CLD");
		pc = pc + 1;
	} else if ((pmem[0] & (~3)) == 0x30) {
		const uint8_t w = pmem[0] & 1;
		const uint8_t d = (pmem[0] >> 1) & 1;
		const uint8_t mod = pmem[1] >> 6;
		const uint8_t reg = (pmem[1] >> 3) & 7;
		const uint8_t rm  = pmem[1] & 7;
		const uint8_t src = (d) ? reg : rm;
		const uint8_t dst = (d) ? rm : reg;

		if (w) {
			if (mod == 3) {
				const uint16_t result =
					memr16le(regs16 + src) ^ memr16le(regs16 + dst);

				memw16le(regs16 + dst, result);
				update_flags16(result, 0, 0, 0);
				printf("XOR %s, %s", reg16name(dst), reg16name(src));
			}
		}

		pc = pc + 2;
	} else if ((pmem[0] & (~1)) == 0xaa) {
		const uint8_t w = pmem[0] & 1;

		if (repeat_prefix) {
			uint16_t cx = memr16le(regs16 + REG_CX);

			while (cx) {
				stos(w);
				cx--;
				memw16le(regs16 + REG_CX, cx);
			}

			printf("REP STOS%c", (w) ? 'W' : 'B');
			repeat_prefix = 0;
		} else {
			stos(w);
			printf("STOS%c", (w) ? 'W' : 'B');
		}

		pc++;
	} else if ((pmem[0] & (~0x18)) == 0x26) {
		segment = (pmem[0] >> 3) & 3;
		segment_prefix = 1;
		pc = pc + 1;
		goto prefix;
	} else if (pmem[0] == 0xf0) {
		pc = pc + 1;
		lock_prefix = 1;
		goto prefix;
	} else if (pmem[0] == 0x90) {
		printf("NOP");
	} else if ((pmem[0] & (~1)) == 0xf2) {
		pc = pc + 1;
		repeat_prefix = 1;
		repeat_zero = pmem[0] & 1;
		goto prefix;
	} else if ((pmem[0] & (~1)) == 0xee) {
		const uint8_t w = pmem[0] & 1;
		const uint16_t port = memr16le(regs16 + REG_DX);

		if (w) {
			const uint16_t val = memr16le(regs16 + REG_AX);

			io_ports[port] = val & 0xff;
			io_ports[port + 1] = val >> 8;
			printf("OUT DX, AX");
		} else {
			io_ports[port] = regs8[REG_AL];
			printf("OUT DX, AL");
		}

		pc = pc + 1;
	} else if ((pmem[0] & (~3)) == 0x80) {
		const uint8_t  s   = (pmem[0] >> 1) & 1;
		const uint8_t  w   = pmem[0] & 1;
		const uint8_t  mod = pmem[1] >> 6;
		const uint8_t  reg = (pmem[1] >> 3) & 7;
		const uint8_t  rm  = pmem[1] & 7;
		const uint16_t segn = (segment_prefix) ? segment : 3;
		const uint16_t seg  = memr16le(regs16 + REG_ES + segn);
		uint16_t pci = 0;

		if (mod == 0) {
			if (rm == 6) {
				const uint16_t addr = direct_addr(pmem + 2);

				if (w) {
					if (s) {
					} else {
					}
				} else {
					const uint8_t cmp = mem[linear(seg, addr)];

					cmpb(cmp, pmem[4]);
					printf("CMP BYTE [%s:%04x], %02x", sregname(segn), addr, pmem[4]);
					pci = 5;
				}
			} else {
			}
		} else if (mod == 3) {
			if (w) {
				const uint16_t v1 = memr16le(regs16 + rm);
				uint16_t v2 = 0;
				
				if (s) {
					v2 = sign_extend(pmem[2]);
					pci = 3;
				} else {
					v2 = memrw(pmem + 2);
					pci = 4;
				}
				cmpw(v1, v2);
				printf("CMP %s, %04x", reg16name(rm), v2);
			} else {
				uint8_t map[] = {
					REG_AL, REG_CL, REG_DL, REG_BL, REG_AH, REG_CH, REG_DH, REG_BH };

				cmpb(regs8[map[rm]], pmem[2]);
				printf("CMP %s, %02x", reg8name(map[rm]), pmem[2]);
				pci = 3;
			}
		}

		pc = pc + pci;
	} else if ((pmem[0] & (~3)) == 0x38) {
		const uint8_t  d    = (pmem[0] >> 1) & 1;
		const uint8_t  w    = pmem[0] & 1;
		const uint8_t  mod  = pmem[1] >> 6;
		const uint8_t  reg  = (pmem[1] >> 3) & 7;
		const uint8_t  rm   = pmem[1] & 7;
		const uint16_t segn = (segment_prefix) ? segment : 3;
		const uint16_t seg  = memr16le(regs16 + REG_ES + segn);
		uint16_t pci = 0;

		if (mod == 0) {
			if (rm == 6) {
				const uint16_t addr = direct_addr(pmem + 2);

				if (d) {
					if (w) {
					} else {
						uint8_t map[] = {
							REG_AL, REG_CL, REG_DL, REG_BL, REG_AH, REG_CH, REG_DH, REG_BH };

						// here...
						cmpb(regs8[map[reg]], mem[linear(seg, addr)]);
						printf("CMP %s, [%s:%04x]", reg8name(map[reg]), sregname(segn), addr);
					}
				}

				pci = 4;
			}
		}

		pc = pc + pci;
	} else if ((pmem[0] & (~1)) == 0x3c) {
		const uint8_t w = pmem[0] & 1;
		unsigned pci = 0;

		if (w) {
			const uint16_t val = memrw(pmem + 1);
			const uint16_t ax = memr16le(regs16 + REG_AX);

			cmpw(ax, val);
			printf("CMP AX, %04x", val);
			pci = 3;
		} else {
			cmpb(regs8[REG_AL], pmem[1]);
			printf("CMP AL, %02x", pmem[1]);
			pci = 2;
		}

		pc = pc + pci;
	} else if (pmem[0] == 0x74) {
		pc = pc + jcb(regs8[FLAG_ZF], pmem[1]);
		printf("JZ %02x", pmem[1]);
	} else if (pmem[0] == 0x75) {
		pc = pc + jcb(!regs8[FLAG_ZF], pmem[1]);
		printf("JNZ %02x", pmem[1]);
	} else if (pmem[0] == 0x77) {
		pc = pc + jcb(regs8[FLAG_ZF] && regs8[FLAG_CF], pmem[1]);
		printf("JA %02x", pmem[1]);
	} else if (pmem[0] == 0x7c) {
		pc = pc + jcb(regs8[FLAG_SF] != regs8[FLAG_OF], pmem[1]);
		printf("JL %02x", pmem[1]);
	} else if (pmem[0] == 0xe9) {
		const uint16_t dl = pmem[1];
		const uint16_t dh = pmem[2];
		const uint16_t disp = (dh << 8) | dl;

		printf("JMP %04x", disp);
		pc = pc + disp;
	} else if ((pmem[0] & (~1)) == 0xfe) {
		const uint8_t  w   = pmem[0] & 1;
		const uint8_t  mod = pmem[1] >> 6;
		const uint8_t  reg = (pmem[1] >> 3) & 7;
		const uint8_t  rm  = pmem[1] & 7;
		const uint16_t segn = (segment_prefix) ? segment : 3;
		const uint16_t seg  = memr16le(regs16 + REG_ES + segn);
		uint16_t pci = 0;

		if (mod == 0) {
			if (rm == 6) {
				const uint16_t addr = direct_addr(pmem + 2);

				if (w) {
					const uint16_t val = memrw(mem + linear(seg, addr));

					memww(mem + linear(seg, addr), val - 1);
					printf("DEC WORD [%s:%04x]", sregname(segn), addr);
				} else {
					const uint8_t val = mem[linear(seg, addr)];

					mem[linear(seg, addr)] = val - 1;
					printf("DEC BYTE [%s:%04x]", sregname(segn), addr);
				}
				pci = 4;
			}
		}

		pc = pc + pci;
	} else if ((pmem[0] & (~7)) == 0x40) {
		const uint8_t  reg = pmem[0] & 7;
		const uint16_t val = memr16le(regs16 + reg);

		memw16le(regs16 + reg, val + 1);
		printf("INC %s", reg16name(reg));

		pc++;
	} else if ((pmem[0] & (~1)) == 0xcc) {
		const uint8_t v = pmem[0] & 1;
		uint16_t addr = 0;

		if (v) {
			const uint16_t val = pmem[1];

			addr = 4 * val;
			printf("INT %02x", pmem[1]);
		} else {
			addr = 0x00c;
			printf("INT");
		}

		pc = intr(v, pc, addr);
	} else if (pmem[0] == 0xe8) {
		const uint16_t disp = memrw(pmem + 1);

		push16(pc + 3);
		printf("CALL %04x", disp);
		pc = pc + disp + 3;
	} else if ((pmem[0] & (~3)) == 0xd0) {
		const uint8_t  w   = pmem[0] & 1;
		const uint8_t  c   = (pmem[0] >> 1) & 1;
		const uint8_t  mod = pmem[1] >> 6;
		const uint8_t  reg = (pmem[1] >> 3) & 7;
		const uint8_t  rm  = pmem[1] & 7;
		const uint16_t segn = (segment_prefix) ? segment : 3;
		const uint16_t seg  = memr16le(regs16 + REG_ES + segn);
		uint16_t pci = 0;

		if (mod == 3) {
			if (c) {
				if (w) {
				} else {
					uint8_t map[] = {
						REG_AL, REG_CL, REG_DL, REG_BL, REG_AH, REG_CH, REG_DH, REG_BH };
					uint8_t bits = regs8[REG_CL];
					uint8_t val = regs8[map[rm]];
					uint8_t i;

					if (reg == 5) {
						while (bits) {
							val = val >> 1;
							bits--;
						}

						regs8[map[rm]] = val;
						printf("SHR %s, CL", reg8name(map[rm]));
						pci = 2;
					}
				}
			} else {
				if (w) {
					const uint16_t val = memr16le(regs16 + rm);

					if (reg == 4) {
						memw16le(regs16 + rm, val << 1);
						printf("SHL %s, 1", reg16name(rm));
						pci = 2;
					}
				}
			}
		}
		pc = pc + pci;
	} else if ((pmem[0] & (~7)) == 0x90) {
		const uint8_t reg = pmem[0] & 7;
		const uint16_t v1 = memr16le(regs16 + REG_AX);
		const uint16_t v2 = memr16le(regs16 + reg);

		memw16le(regs16 + REG_AX, v2);
		memw16le(regs16 + reg, v1);

		printf("XCHG AX, %s", reg16name(reg));
		pc++;
	} else if ((pmem[0] & (~1)) == 0x86) {
		const uint8_t  w    = pmem[0] & 1;
		const uint8_t  mod  = pmem[1] >> 6;
		const uint8_t  reg  = (pmem[1] >> 3) & 7;
		const uint8_t  rm   = pmem[1] & 7;
		const uint16_t segn = (segment_prefix) ? segment : 3;
		const uint16_t seg  = memr16le(regs16 + REG_ES + segn);
		uint16_t pci = 0;

		if (mod == 3) {
			if (w) {
			} else {
				const uint8_t map[] = {
					REG_AL, REG_CL, REG_DL, REG_BL, REG_AH, REG_CH, REG_DH, REG_BH };
				const uint8_t v1 = regs8[map[reg]];
				const uint8_t v2 = regs8[map[rm]];

				regs8[map[rm]]  = v1;
				regs8[map[reg]] = v2;
				printf("XCHG %s, %s", reg8name(map[reg]), reg8name(map[rm]));	
				pci = 2;
			}
		}
		pc = pc + pci;
	}

	printf("\n           ------\n");
	return pc;
}

// Emulator entry point
int main(int argc, char *argv[])
{
	// regs16 and reg8 point to F000:0, the start of memory-mapped registers. CS is initialised to F000
	regs8 = mem + REGS_BASE;
	regs16 = (uint16_t *)regs8;
	memw16le(regs16 + REG_CS, 0xF000);

	// Trap flag off
	regs8[FLAG_TF] = 0;

	// Set DL equal to the boot device: 0 for the FD, or 0x80 for the HD. Normally, boot from the FD.
	// But, if the HD image file is prefixed with @, then boot from the HD
	regs8[REG_DL] = ((argc > 3) && (*argv[3] == '@')) ? argv[3]++, 0x80 : 0;

	// Open BIOS (file id disk[2]), floppy disk image (disk[1]), and hard disk image (disk[0]) if specified
	for (file_index = 3; file_index;)
		disk[--file_index] = *++argv ? open(*argv, 32898) : 0;

	// Set CX:AX equal to the hard disk image size, if present
	memw32le((uint32_t *)(regs16 + REG_AX), *disk ? lseek(*disk, 0, 2) >> 9 : 0);

	// Load BIOS image into F000:0100, and set IP to 0100
	read(disk[2], regs8 + (reg_ip = 0x100), 0xFF00);

	// Load instruction decoding helper table
	for (int i = 0; i < 20; i++)
		for (int j = 0; j < 256; j++)
			bios_table_lookup[i][j] = regs8[memr16le(regs16 + 0x81 + i) + j];

	// first decode
	while (memr16le(regs16 + REG_CS) != 0 || reg_ip != 0) {
		const uint16_t old_reg_ip = reg_ip;

		reg_ip = decode(mem, reg_ip);
		if (reg_ip == old_reg_ip) {
			printf("\nINFINITE LOOP\n");
			return 0;
		}
	}

	// Instruction execution loop. Terminates if CS:IP = 0:0
	for (; opcode_stream = mem + 16 * memr16le(regs16 + REG_CS) + reg_ip, opcode_stream != mem;)
	{

		// Set up variables to prepare for decoding an opcode
		set_opcode(*opcode_stream);

		// Extract i_w and i_d fields from instruction
		i_w = (i_reg4bit = raw_opcode_id & 7) & 1;
		i_d = i_reg4bit / 2 & 1;

		// Extract instruction data fields
		i_data0 = memr16le((uint16_t *) (opcode_stream + 1));
		i_data1 = memr16le((uint16_t *) (opcode_stream + 2));
		i_data2 = memr16le((uint16_t *) (opcode_stream + 3));

		// seg_override_en and rep_override_en contain number of instructions to hold segment override and REP prefix respectively
		if (seg_override_en)
			seg_override_en--;
		if (rep_override_en)
			rep_override_en--;

		// i_mod_size > 0 indicates that opcode uses i_mod/i_rm/i_reg, so decode them
		if (i_mod_size)
		{
			i_mod = (i_data0 & 0xFF) >> 6;
			i_rm = i_data0 & 7;
			i_reg = i_data0 / 8 & 7;

			if ((!i_mod && i_rm == 6) || (i_mod == 2))
				i_data2 = memr16le((uint16_t *) (opcode_stream + 4));
			else if (i_mod != 1)
				i_data2 = i_data1;
			else // If i_mod is 1, operand is (usually) 8 bits rather than 16 bits
				i_data1 = i_data1 & 0xff;

			DECODE_RM_REG;
		}

		// Instruction execution unit
		switch (xlat_opcode_id)
		{
			OPCODE_CHAIN 0: // Conditional jump (JAE, JNAE, etc.)
				// i_w is the invert flag, e.g. i_w == 1 means JNAE, whereas i_w == 0 means JAE 
				scratch_uchar = raw_opcode_id / 2 & 7;
				reg_ip += (char)i_data0 * (i_w ^ (regs8[bios_table_lookup[TABLE_COND_JUMP_DECODE_A][scratch_uchar]] || regs8[bios_table_lookup[TABLE_COND_JUMP_DECODE_B][scratch_uchar]] || regs8[bios_table_lookup[TABLE_COND_JUMP_DECODE_C][scratch_uchar]] ^ regs8[bios_table_lookup[TABLE_COND_JUMP_DECODE_D][scratch_uchar]]))
			OPCODE 1: // MOV reg, imm
				i_w = !!(raw_opcode_id & 8);
				R_M_OP(mem[GET_REG_ADDR(i_reg4bit)], =, i_data0)
			OPCODE 3: // PUSH regs16
				R_M_PUSH(regs16[i_reg4bit])
			OPCODE 4: // POP regs16
				R_M_POP(regs16[i_reg4bit])
			OPCODE 2: // INC|DEC regs16
				i_w = 1;
				i_d = 0;
				i_reg = i_reg4bit;
				DECODE_RM_REG;
				i_reg = extra
			OPCODE_CHAIN 5: // INC|DEC|JMP|CALL|PUSH
				if (i_reg < 2) // INC|DEC
					MEM_OP(op_from_addr, += 1 - 2 * i_reg +, REGS_BASE + 2 * REG_ZERO),
					op_source = 1,
					set_AF_OF_arith(),
					set_OF(op_dest + 1 - i_reg == 1 << (TOP_BIT - 1)),
					(xlat_opcode_id == 5) && (set_opcode(0x10), 0); // Decode like ADC
				else if (i_reg != 6) // JMP|CALL
					i_reg - 3 || R_M_PUSH(regs16[REG_CS]), // CALL (far)
					i_reg & 2 && R_M_PUSH(reg_ip + 2 + i_mod*(i_mod != 3) + 2*(!i_mod && i_rm == 6)), // CALL (near or far)
					i_reg & 1 && (regs16[REG_CS] = CAST(short)mem[op_from_addr + 2]), // JMP|CALL (far)
					R_M_OP(reg_ip, =, mem[op_from_addr]),
					set_opcode(0x9A); // Decode like CALL
				else // PUSH
					R_M_PUSH(mem[rm_addr])
			OPCODE 6: // TEST r/m, imm16 / NOT|NEG|MUL|IMUL|DIV|IDIV reg
				op_to_addr = op_from_addr;

				switch (i_reg)
				{
					OPCODE_CHAIN 0: // TEST
						set_opcode(0x20); // Decode like AND
						reg_ip += i_w + 1;
						R_M_OP(mem[op_to_addr], &, i_data2)
					OPCODE 2: // NOT
						OP(=~)
					OPCODE 3: // NEG
						OP(=-);
						op_dest = 0;
						set_opcode(0x28); // Decode like SUB
						set_CF(op_result > op_dest)
					OPCODE 4: // MUL
						i_w ? MUL_MACRO(unsigned short, regs16) : MUL_MACRO(unsigned char, regs8)
					OPCODE 5: // IMUL
						i_w ? MUL_MACRO(short, regs16) : MUL_MACRO(char, regs8)
					OPCODE 6: // DIV
						i_w ? DIV_MACRO(unsigned short, unsigned, regs16) : DIV_MACRO(unsigned char, unsigned short, regs8)
					OPCODE 7: // IDIV
						i_w ? DIV_MACRO(short, int, regs16) : DIV_MACRO(char, short, regs8);
				}
			OPCODE 7: // ADD|OR|ADC|SBB|AND|SUB|XOR|CMP AL/AX, immed
				rm_addr = REGS_BASE;
				i_data2 = i_data0;
				i_mod = 3;
				i_reg = extra;
				reg_ip--;
			OPCODE_CHAIN 8: // ADD|OR|ADC|SBB|AND|SUB|XOR|CMP reg, immed
				op_to_addr = rm_addr;
				regs16[REG_SCRATCH] = (i_d |= !i_w) ? (char)i_data2 : i_data2;
				op_from_addr = REGS_BASE + 2 * REG_SCRATCH;
				reg_ip += !i_d + 1;
				set_opcode(0x08 * (extra = i_reg));
			OPCODE_CHAIN 9: // ADD|OR|ADC|SBB|AND|SUB|XOR|CMP|MOV reg, r/m
				switch (extra)
				{
					OPCODE_CHAIN 0: // ADD
						OP(+=),
						set_CF(op_result < op_dest)
					OPCODE 1: // OR
						OP(|=)
					OPCODE 2: // ADC
						ADC_SBB_MACRO(+)
					OPCODE 3: // SBB
						ADC_SBB_MACRO(-)
					OPCODE 4: // AND
						OP(&=)
					OPCODE 5: // SUB
						OP(-=),
						set_CF(op_result > op_dest)
					OPCODE 6: // XOR
						OP(^=)
					OPCODE 7: // CMP
						OP(-),
						set_CF(op_result > op_dest)
					OPCODE 8: // MOV
						OP(=);
				}
			OPCODE 10: // MOV sreg, r/m | POP r/m | LEA reg, r/m
				if (!i_w) // MOV
					i_w = 1,
					i_reg += 8,
					DECODE_RM_REG,
					OP(=);
				else if (!i_d) // LEA
					seg_override_en = 1,
					seg_override = REG_ZERO,
					DECODE_RM_REG,
					R_M_OP(mem[op_from_addr], =, rm_addr);
				else // POP
					R_M_POP(mem[rm_addr])
			OPCODE 11: // MOV AL/AX, [loc]
				i_mod = i_reg = 0;
				i_rm = 6;
				i_data1 = i_data0;
				DECODE_RM_REG;
				MEM_OP(op_from_addr, =, op_to_addr)
			OPCODE 12: // ROL|ROR|RCL|RCR|SHL|SHR|???|SAR reg/mem, 1/CL/imm (80186)
				scratch2_uint = SIGN_OF(mem[rm_addr]),
				scratch_uint = extra ? // xxx reg/mem, imm
					++reg_ip,
					(char)i_data1
				: // xxx reg/mem, CL
					i_d
						? 31 & regs8[REG_CL]
				: // xxx reg/mem, 1
					1;
				if (scratch_uint)
				{
					if (i_reg < 4) // Rotate operations
						scratch_uint %= i_reg / 2 + TOP_BIT,
						R_M_OP(scratch2_uint, =, mem[rm_addr]);
					if (i_reg & 1) // Rotate/shift right operations
						R_M_OP(mem[rm_addr], >>=, scratch_uint);
					else // Rotate/shift left operations
						R_M_OP(mem[rm_addr], <<=, scratch_uint);
					if (i_reg > 3) // Shift operations
						set_opcode(0x10); // Decode like ADC
					if (i_reg > 4) // SHR or SAR
						set_CF(op_dest >> (scratch_uint - 1) & 1);
				}

				switch (i_reg)
				{
					OPCODE_CHAIN 0: // ROL
						R_M_OP(mem[rm_addr], += , scratch2_uint >> (TOP_BIT - scratch_uint));
						set_OF(SIGN_OF(op_result) ^ set_CF(op_result & 1))
					OPCODE 1: // ROR
						scratch2_uint &= (1 << scratch_uint) - 1,
						R_M_OP(mem[rm_addr], += , scratch2_uint << (TOP_BIT - scratch_uint));
						set_OF(SIGN_OF(op_result * 2) ^ set_CF(SIGN_OF(op_result)))
					OPCODE 2: // RCL
						R_M_OP(mem[rm_addr], += (regs8[FLAG_CF] << (scratch_uint - 1)) + , scratch2_uint >> (1 + TOP_BIT - scratch_uint));
						set_OF(SIGN_OF(op_result) ^ set_CF(scratch2_uint & 1 << (TOP_BIT - scratch_uint)))
					OPCODE 3: // RCR
						R_M_OP(mem[rm_addr], += (regs8[FLAG_CF] << (TOP_BIT - scratch_uint)) + , scratch2_uint << (1 + TOP_BIT - scratch_uint));
						set_CF(scratch2_uint & 1 << (scratch_uint - 1));
						set_OF(SIGN_OF(op_result) ^ SIGN_OF(op_result * 2))
					OPCODE 4: // SHL
						set_OF(SIGN_OF(op_result) ^ set_CF(SIGN_OF(op_dest << (scratch_uint - 1))))
					OPCODE 5: // SHR
						set_OF(SIGN_OF(op_dest))
					OPCODE 7: // SAR
						scratch_uint < TOP_BIT || set_CF(scratch2_uint);
						set_OF(0);
						R_M_OP(mem[rm_addr], +=, scratch2_uint *= ~(((1 << TOP_BIT) - 1) >> scratch_uint));
				}
			OPCODE 13: // LOOPxx|JCZX
				scratch_uint = !!--regs16[REG_CX];

				switch(i_reg4bit)
				{
					OPCODE_CHAIN 0: // LOOPNZ
						scratch_uint &= !regs8[FLAG_ZF]
					OPCODE 1: // LOOPZ
						scratch_uint &= regs8[FLAG_ZF]
					OPCODE 3: // JCXXZ
						scratch_uint = !++regs16[REG_CX];
				}
				reg_ip += scratch_uint*(char)i_data0
			OPCODE 14: // JMP | CALL short/near
				reg_ip += 3 - i_d;
				if (!i_w)
				{
					if (i_d) // JMP far
						reg_ip = 0,
						regs16[REG_CS] = i_data2;
					else // CALL
						R_M_PUSH(reg_ip);
				}
				reg_ip += i_d && i_w ? (char)i_data0 : i_data0
			OPCODE 15: // TEST reg, r/m
				MEM_OP(op_from_addr, &, op_to_addr)
			OPCODE 16: // XCHG AX, regs16
				i_w = 1;
				op_to_addr = REGS_BASE;
				op_from_addr = GET_REG_ADDR(i_reg4bit);
			OPCODE_CHAIN 24: // NOP|XCHG reg, r/m
				if (op_to_addr != op_from_addr)
					OP(^=),
					MEM_OP(op_from_addr, ^=, op_to_addr),
					OP(^=)
			OPCODE 17: // MOVSx (extra=0)|STOSx (extra=1)|LODSx (extra=2)
				scratch2_uint = seg_override_en ? seg_override : REG_DS;

				for (scratch_uint = rep_override_en ? regs16[REG_CX] : 1; scratch_uint; scratch_uint--)
				{
					MEM_OP(extra < 2 ? SEGREG(REG_ES, REG_DI,) : REGS_BASE, =, extra & 1 ? REGS_BASE : SEGREG(scratch2_uint, REG_SI,)),
					extra & 1 || INDEX_INC(REG_SI),
					extra & 2 || INDEX_INC(REG_DI);
				}

				if (rep_override_en)
					regs16[REG_CX] = 0
			OPCODE 18: // CMPSx (extra=0)|SCASx (extra=1)
				scratch2_uint = seg_override_en ? seg_override : REG_DS;

				if ((scratch_uint = rep_override_en ? regs16[REG_CX] : 1))
				{
					for (; scratch_uint; rep_override_en || scratch_uint--)
					{
						MEM_OP(extra ? REGS_BASE : SEGREG(scratch2_uint, REG_SI,), -, SEGREG(REG_ES, REG_DI,)),
						extra || INDEX_INC(REG_SI),
						INDEX_INC(REG_DI), rep_override_en && !(--regs16[REG_CX] && (!op_result == rep_mode)) && (scratch_uint = 0);
					}

					set_flags_type = FLAGS_UPDATE_SZP | FLAGS_UPDATE_AO_ARITH; // Funge to set SZP/AO flags
					set_CF(op_result > op_dest);
				}
			OPCODE 19: // RET|RETF|IRET
				i_d = i_w;
				R_M_POP(reg_ip);
				if (extra) // IRET|RETF|RETF imm16
					R_M_POP(regs16[REG_CS]);
				if (extra & 2) // IRET
					set_flags(R_M_POP(scratch_uint));
				else if (!i_d) // RET|RETF imm16
					regs16[REG_SP] += i_data0
			OPCODE 20: // MOV r/m, immed
				R_M_OP(mem[op_from_addr], =, i_data2)
			OPCODE 21: // IN AL/AX, DX/imm8
				io_ports[0x20] = 0; // PIC EOI
				io_ports[0x42] = --io_ports[0x40]; // PIT channel 0/2 read placeholder
				io_ports[0x3DA] ^= 9; // CGA refresh
				scratch_uint = extra ? regs16[REG_DX] : (unsigned char)i_data0;
				scratch_uint == 0x60 && (io_ports[0x64] = 0); // Scancode read flag
				scratch_uint == 0x3D5 && (io_ports[0x3D4] >> 1 == 7) && (io_ports[0x3D5] = ((mem[0x49E]*80 + mem[0x49D] + CAST(short)mem[0x4AD]) & (io_ports[0x3D4] & 1 ? 0xFF : 0xFF00)) >> (io_ports[0x3D4] & 1 ? 0 : 8)); // CRT cursor position
				R_M_OP(regs8[REG_AL], =, io_ports[scratch_uint]);
			OPCODE 22: // OUT DX/imm8, AL/AX
				scratch_uint = extra ? regs16[REG_DX] : (unsigned char)i_data0;
				R_M_OP(io_ports[scratch_uint], =, regs8[REG_AL]);
				scratch_uint == 0x61 && (io_hi_lo = 0, spkr_en |= regs8[REG_AL] & 3); // Speaker control
				(scratch_uint == 0x40 || scratch_uint == 0x42) && (io_ports[0x43] & 6) && (mem[0x469 + scratch_uint - (io_hi_lo ^= 1)] = regs8[REG_AL]); // PIT rate programming
				scratch_uint == 0x3D5 && (io_ports[0x3D4] >> 1 == 6) && (mem[0x4AD + !(io_ports[0x3D4] & 1)] = regs8[REG_AL]); // CRT video RAM start offset
				scratch_uint == 0x3D5 && (io_ports[0x3D4] >> 1 == 7) && (scratch2_uint = ((mem[0x49E]*80 + mem[0x49D] + CAST(short)mem[0x4AD]) & (io_ports[0x3D4] & 1 ? 0xFF00 : 0xFF)) + (regs8[REG_AL] << (io_ports[0x3D4] & 1 ? 0 : 8)) - CAST(short)mem[0x4AD], mem[0x49D] = scratch2_uint % 80, mem[0x49E] = scratch2_uint / 80); // CRT cursor position
				scratch_uint == 0x3B5 && io_ports[0x3B4] == 1 && (GRAPHICS_X = regs8[REG_AL] * 16); // Hercules resolution reprogramming. Defaults are set in the BIOS
				scratch_uint == 0x3B5 && io_ports[0x3B4] == 6 && (GRAPHICS_Y = regs8[REG_AL] * 4);
			OPCODE 23: // REPxx
				rep_override_en = 2;
				rep_mode = i_w;
				seg_override_en && seg_override_en++
			OPCODE 25: // PUSH reg
				R_M_PUSH(regs16[extra])
			OPCODE 26: // POP reg
				R_M_POP(regs16[extra])
			OPCODE 27: // xS: segment overrides
				seg_override_en = 2;
				seg_override = extra;
				rep_override_en && rep_override_en++
			OPCODE 28: // DAA/DAS
				i_w = 0;
				extra ? DAA_DAS(-=, >=, 0xFF, 0x99) : DAA_DAS(+=, <, 0xF0, 0x90) // extra = 0 for DAA, 1 for DAS
			OPCODE 29: // AAA/AAS
				op_result = AAA_AAS(extra - 1)
			OPCODE 30: // CBW
				regs8[REG_AH] = -SIGN_OF(regs8[REG_AL])
			OPCODE 31: // CWD
				regs16[REG_DX] = -SIGN_OF(regs16[REG_AX])
			OPCODE 32: // CALL FAR imm16:imm16
				R_M_PUSH(regs16[REG_CS]);
				R_M_PUSH(reg_ip + 5);
				regs16[REG_CS] = i_data2;
				reg_ip = i_data0
			OPCODE 33: // PUSHF
				make_flags();
				R_M_PUSH(scratch_uint)
			OPCODE 34: // POPF
				set_flags(R_M_POP(scratch_uint))
			OPCODE 35: // SAHF
				make_flags();
				set_flags((scratch_uint & 0xFF00) + regs8[REG_AH])
			OPCODE 36: // LAHF
				make_flags(),
				regs8[REG_AH] = scratch_uint
			OPCODE 37: // LES|LDS reg, r/m
				i_w = i_d = 1;
				DECODE_RM_REG;
				OP(=);
				MEM_OP(REGS_BASE + extra, =, rm_addr + 2)
			OPCODE 38: // INT 3
				++reg_ip;
				pc_interrupt(3)
			OPCODE 39: // INT imm8
				reg_ip += 2;
				pc_interrupt(i_data0)
			OPCODE 40: // INTO
				++reg_ip;
				regs8[FLAG_OF] && pc_interrupt(4)
			OPCODE 41: // AAM
				if (i_data0 &= 0xFF)
					regs8[REG_AH] = regs8[REG_AL] / i_data0,
					op_result = regs8[REG_AL] %= i_data0;
				else // Divide by zero
					pc_interrupt(0)
			OPCODE 42: // AAD
				i_w = 0;
				regs16[REG_AX] = op_result = 0xFF & regs8[REG_AL] + i_data0 * regs8[REG_AH]
			OPCODE 43: // SALC
				regs8[REG_AL] = -regs8[FLAG_CF]
			OPCODE 44: // XLAT
				regs8[REG_AL] = mem[SEGREG(seg_override_en ? seg_override : REG_DS, REG_BX, regs8[REG_AL] +)]
			OPCODE 45: // CMC
				regs8[FLAG_CF] ^= 1
			OPCODE 46: // CLC|STC|CLI|STI|CLD|STD
				regs8[extra / 2] = extra & 1
			OPCODE 47: // TEST AL/AX, immed
				R_M_OP(regs8[REG_AL], &, i_data0)
			OPCODE 48: // Emulator-specific 0F xx opcodes
				switch ((char)i_data0)
				{
					OPCODE_CHAIN 0: // PUTCHAR_AL
						write(1, regs8, 1)
					OPCODE 1: // GET_RTC
						time(&clock_buf);
						ftime(&ms_clock);
						memcpy(mem + SEGREG(REG_ES, REG_BX,), localtime(&clock_buf), sizeof(struct tm));
						CAST(short)mem[SEGREG(REG_ES, REG_BX, 36+)] = ms_clock.millitm;
					OPCODE 2: // DISK_READ
					OPCODE_CHAIN 3: // DISK_WRITE
						regs8[REG_AL] = ~lseek(disk[regs8[REG_DL]], CAST(unsigned)regs16[REG_BP] << 9, 0)
							? ((char)i_data0 == 3 ? (int(*)())write : (int(*)())read)(disk[regs8[REG_DL]], mem + SEGREG(REG_ES, REG_BX,), regs16[REG_AX])
							: 0;
				}
		}

		// Increment instruction pointer by computed instruction length. Tables in the BIOS binary
		// help us here.
		reg_ip += (i_mod*(i_mod != 3) + 2*(!i_mod && i_rm == 6))*i_mod_size + bios_table_lookup[TABLE_BASE_INST_SIZE][raw_opcode_id] + bios_table_lookup[TABLE_I_W_SIZE][raw_opcode_id]*(i_w + 1);

		// If instruction needs to update SF, ZF and PF, set them as appropriate
		if (set_flags_type & FLAGS_UPDATE_SZP)
		{
			regs8[FLAG_SF] = SIGN_OF(op_result);
			regs8[FLAG_ZF] = !op_result;
			regs8[FLAG_PF] = bios_table_lookup[TABLE_PARITY_FLAG][(unsigned char)op_result];

			// If instruction is an arithmetic or logic operation, also set AF/OF/CF as appropriate.
			if (set_flags_type & FLAGS_UPDATE_AO_ARITH)
				set_AF_OF_arith();
			if (set_flags_type & FLAGS_UPDATE_OC_LOGIC)
				set_CF(0), set_OF(0);
		}

		// Poll timer/keyboard every KEYBOARD_TIMER_UPDATE_DELAY instructions
		if (!(++inst_counter % KEYBOARD_TIMER_UPDATE_DELAY))
			int8_asap = 1;

		// Application has set trap flag, so fire INT 1
		if (trap_flag)
			pc_interrupt(1);

		trap_flag = regs8[FLAG_TF];

		// If a timer tick is pending, interrupts are enabled, and no overrides/REP are active,
		// then process the tick and check for new keystrokes
		if (int8_asap && !seg_override_en && !rep_override_en && regs8[FLAG_IF] && !regs8[FLAG_TF]) {
			pc_interrupt(0xA);
			int8_asap = 0;
			// Keyboard driver for console. This may need changing for UNIX/non-UNIX platforms
			printf("wait for keyboard...\n"); fflush(stdout);
			read(0, mem + 0x4A6, 1) && (int8_asap = (mem[0x4A6] == 0x1B), pc_interrupt(7));
		}
	}

	return 0;
}
