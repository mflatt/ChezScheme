#include "../ta6osx/boot/ta6osx/equates.h"
#include "../ta6osx/boot/ta6osx/scheme.h"
#include <string.h>
#include <math.h>

typedef struct instructtion_t {
  union {
    struct {
      unsigned char op;
    } any;
    struct {
      unsigned char op;
      unsigned char dest;
      short imm;
    } di;
    struct {
      unsigned char op;
      unsigned char dest;
      short reg;
    } dr;
    struct {
      unsigned char op;
      unsigned char dest:4;
      unsigned char reg1:4;
      short reg2;
    } drr;
    struct {
      unsigned char op;
      unsigned char dest:4;
      unsigned char reg:4;
      short imm;
    } dri;
  };
} instruction_t;

static uptr regs[8];
static double fpregs[8];

ptr S_pb_interp(void *bytecode) {
  instruction_t *instr = (instruction_t *)bytecode, *next_instr;
  int flag = 0;

  while (1) {
    next_instr = string + 1;
    switch(instr->any.op) {
    case pb_mov16_pb_zero_bits_pb_shift0:
      regs[instr->di.dest] = (uptr)instr->di.imm;
      break;
    case pb_mov16_pb_zero_bits_pb_shift1:
      regs[instr->di.dest] = (uptr)instr->di.imm << 16;
      break;
    case pb_mov16_pb_zero_bits_pb_shift2:
      regs[instr->di.dest] = (uptr)instr->di.imm << 32;
      break;
    case pb_mov16_pb_zero_bits_pb_shift3:
      regs[instr->di.dest] = (uptr)instr->di.imm << 48;
      break;
    case pb_mov16_pb_keep_bits_pb_shift0:
      regs[instr->di.dest] |= (uptr)instr->di.imm;
      break;
    case pb_mov16_pb_keep_bits_pb_shift1:
      regs[instr->di.dest] |= (uptr)instr->di.imm << 16;
      break;
    case pb_mov16_pb_keep_bits_pb_shift2:
      regs[instr->di.dest] |= (uptr)instr->di.imm << 32;
      break;
    case pb_mov16_pb_keep_bits_pb_shift3:
      regs[instr->di.dest] |= (uptr)instr->di.imm << 48;
      break;
    case pb_mov_pb_i_i:
      regs[instr->dr.dest] = regs[instr->dr.reg];
      break;
    case pb_mov_pb_d_d:
      fpregs[instr->dr.dest] = fpregs[instr->dr.reg];
      break;
    case pb_mov_pb_i_d:
      memcpy(&fpregs[instr->dr.dest], &regs[instr->dr.reg], sizeof(double));
      break;
    case pb_mov_pb_d_i:
      memcpy(&regs[instr->dr.dest], &fpregs[instr->dr.reg], sizeof(double));
      break;
    case pb_mov_pb_s_d:
      {
        float f;
        memcpy(&f, &fpregs[instr->dr.reg], sizeof(float)); /* litte endian */
        fpregs[instr->dr.dest] = f;
      }
      break;
    case pb_mov_pb_d_s:
      {
        float f;
        f = fpregs[instr->dr.reg];
        memcpy(&fpregs[instr->dr.dest], &f, sizeof(float)); /* litte endian */
      }
      break;
    case pb_bin_op_pb_no_signal_pb_add_pb_register:
      regs[instr->drr.dest] = regs[instr->drr.reg1] + regs[instr->drr.reg2];
      break;
    case pb_bin_op_pb_no_signal_pb_add_pb_immediate:
      regs[instr->dri.dest] = regs[instr->dri.reg] + (uptr)instr->dri.imm;
      break;
    case pb_bin_op_pb_no_signal_pb_sub_pb_register:
      regs[instr->drr.dest] = regs[instr->drr.reg1] - regs[instr->drr.reg2];
      break;
    case pb_bin_op_pb_no_signal_pb_sub_pb_immediate:
      regs[instr->dri.dest] = regs[instr->dri.reg] - (uptr)instr->dri.imm;
      break;
    case pb_bin_op_pb_no_signal_pb_mul_pb_register:
      regs[instr->drr.dest] = regs[instr->drr.reg1] * regs[instr->drr.reg2];
      break;
    case pb_bin_op_pb_no_signal_pb_mul_pb_immediate:
      regs[instr->dri.dest] = (uptr)regs[instr->dri.reg] * (uptr)instr->dri.imm;
      break;
    case pb_bin_op_pb_no_signal_pb_div_pb_register:
      regs[instr->drr.dest] = (iptr)regs[instr->drr.reg1] / (iptr)regs[instr->drr.reg2];
      break;
    case pb_bin_op_pb_no_signal_pb_div_pb_immediate:
      regs[instr->dri.dest] = (iptr)regs[instr->dri.reg] / (iptr)instr->dri.imm;
      break;
    case pb_bin_op_pb_no_signal_pb_and_pb_register:
      regs[instr->drr.dest] = regs[instr->drr.reg1] & regs[instr->drr.reg2];
      break;
    case pb_bin_op_pb_no_signal_pb_and_pb_immediate:
      regs[instr->dri.dest] = regs[instr->dri.reg] & (uptr)instr->dri.imm;
      break;
    case pb_bin_op_pb_no_signal_pb_ior_pb_register:
      regs[instr->drr.dest] = regs[instr->drr.reg1] | regs[instr->drr.reg2];
      break;
    case pb_bin_op_pb_no_signal_pb_ior_pb_immediate:
      regs[instr->dri.dest] = regs[instr->dri.reg] | (uptr)instr->dri.imm;
      break;
    case pb_bin_op_pb_no_signal_pb_xor_pb_register:
      regs[instr->drr.dest] = regs[instr->drr.reg1] ^ regs[instr->drr.reg2];
      break;
    case pb_bin_op_pb_no_signal_pb_xor_pb_immediate:
      regs[instr->dri.dest] = regs[instr->dri.reg] ^ (uptr)instr->dri.imm;
      break;
    case pb_bin_op_pb_no_signal_pb_lsl_pb_register:
      regs[instr->drr.dest] = regs[instr->drr.reg1] << regs[instr->drr.reg2];
      break;
    case pb_bin_op_pb_no_signal_pb_lsl_pb_immediate:
      regs[instr->dri.dest] = regs[instr->dri.reg] << instr->dri.imm;
      break;
    case pb_bin_op_pb_no_signal_pb_lsr_pb_register:
      regs[instr->drr.dest] = regs[instr->drr.reg1] >> regs[instr->drr.reg2];
      break;
    case pb_bin_op_pb_no_signal_pb_lsr_pb_immediate:
      regs[instr->dri.dest] = regs[instr->dri.reg] >> instr->dri.imm;
      break;
    case pb_bin_op_pb_no_signal_pb_asr_pb_register:
      regs[instr->drr.dest] = (iptr)regs[instr->drr.reg1] >> regs[instr->drr.reg2];
      break;
    case pb_bin_op_pb_no_signal_pb_asr_pb_immediate:
      regs[instr->dri.dest] = (iptr)regs[instr->dri.reg] >> instr->dri.imm;
      break;
    case pb_bin_op_pb_signal_pb_add_pb_register:
      {
        uptr a = regs[instr->drr.reg1];
        uptr b = regs[instr->drr.reg2];
        uptr r = a + b;
        regs[instr->drr.dest] = r;
        flag = (b != r - a);
      }
      break;
    case pb_bin_op_pb_signal_pb_add_pb_immediate:
      {
        uptr a = regs[instr->dri.reg];
        uptr b = (uptr)instr->dri.imm;
        uptr r = a + b;
        regs[instr->dri.dest] = r;
        flag = (b != r - a);
      }
      break;
    case pb_bin_op_pb_signal_pb_sub_pb_register:
      {
        uptr a = regs[instr->drr.reg1];
        uptr b = regs[instr->drr.reg2];
        uptr r = a - b;
        regs[instr->drr.dest] = r;
        flag = (a != r + b);
      }
      break;
    case pb_bin_op_pb_signal_pb_sub_pb_immediate:
      {
        uptr a = regs[instr->dri.reg];
        uptr b = (uptr)instr->dri.imm;
        uptr r = a - b;
        regs[instr->dri.dest] = r;
        flag = (a != r + b);
      }
      break;
    case pb_bin_op_pb_signal_pb_mul_pb_register:
      {
        uptr a = regs[instr->drr.reg1];
        uptr b = regs[instr->drr.reg2];
        uptr r = a * b;
        regs[instr->drr.dest] = r;
        if (b == (uptr)-1)
          flag = (a != r * (uptr)-1);
        else
          flag = (a != r / b);
      }
      break;
    case pb_bin_op_pb_signal_pb_mul_pb_immediate:
      {
        uptr a = regs[instr->dri.reg];
        uptr b = (uptr)instr->dri.imm;
        uptr r = a * b;
        regs[instr->dri.dest] = r;
        if (b == (uptr)-1)
          flag = (a != r * (uptr)-1);
        else
          flag = (a != r / b);
      }
      break;
    case pb_cmp_op_pb_eq_pb_register:
      flag = regs[instr->dr.dest] == regs[instr->dr.reg];
      break;
    case pb_cmp_op_pb_eq_pb_immediate:
      flag = regs[instr->di.dest] == instr->di.imm;
      break;
    case pb_cmp_op_pb_lt_pb_register:
      flag = (iptr)regs[instr->dr.dest] < (iptr)regs[instr->dr.reg];
      break;
    case pb_cmp_op_pb_lt_pb_immediate:
      flag = (iptr)regs[instr->di.dest] < (iptr)instr->di.imm;
      break;
    case pb_cmp_op_pb_gt_pb_register:
      flag = (iptr)regs[instr->dr.dest] > (iptr)regs[instr->dr.reg];
      break;
    case pb_cmp_op_pb_gt_pb_immediate:
      flag = (iptr)regs[instr->di.dest] > (iptr)instr->di.imm;
      break;
    case pb_cmp_op_pb_le_pb_register:
      flag = (iptr)regs[instr->dr.dest] <= (iptr)regs[instr->dr.reg];
      break;
    case pb_cmp_op_pb_le_pb_immediate:
      flag = (iptr)regs[instr->di.dest] <= (iptr)instr->di.imm;
      break;
    case pb_cmp_op_pb_ge_pb_register:
      flag = (iptr)regs[instr->dr.dest] >= (iptr)regs[instr->dr.reg];
      break;
    case pb_cmp_op_pb_ge_pb_immediate:
      flag = (iptr)regs[instr->di.dest] >= (iptr)instr->di.imm;
      break;
    case pb_cmp_op_pb_ab_pb_register:
      flag = regs[instr->dr.dest] > regs[instr->dr.reg];
      break;
    case pb_cmp_op_pb_ab_pb_immediate:
      flag = regs[instr->di.dest] > (uptr)instr->di.imm;
      break;
    case pb_cmp_op_pb_bl_pb_register:
      flag = regs[instr->dr.dest] < regs[instr->dr.reg];
      break;
    case pb_cmp_op_pb_bl_pb_immediate:
      flag = regs[instr->di.dest] < (uptr)instr->di.imm;
      break;
    case pb_fp_bin_op_pb_add_pb_register:
      fpregs[instr->drr.dest] = fpregs[instr->drr.reg1] + fpregs[instr->drr.reg2];
      break;
    case pb_fp_bin_op_pb_sub_pb_register:
      fpregs[instr->drr.dest] = fpregs[instr->drr.reg1] - fpregs[instr->drr.reg2];
      break;
    case pb_fp_bin_op_pb_mul_pb_register:
      fpregs[instr->drr.dest] = fpregs[instr->drr.reg1] * fpregs[instr->drr.reg2];
      break;
    case pb_fp_bin_op_pb_div_pb_register:
      fpregs[instr->drr.dest] = fpregs[instr->drr.reg1] / fpregs[instr->drr.reg2];
      break;
    case pb_un_op_pb_not_pb_register:
      regs[instr->dr.dest] = ~(regs[instr->dr.reg]);
      break;
    case pb_un_op_pb_not_pb_immediate:
      regs[instr->di.dest] = ~((uptr)instr->di.imm);
      break;
    case pb_fp_un_op_pb_sqrt_pb_register:
      fpregs[instr->dr.dest] = sqrt(fpregs[instr->dr.reg]);
      break;
    case pb_fp_cmp_op_pb_eq_pb_register:
      flag = fpregs[instr->dr.dest] == fpregs[instr->dr.reg];
      break;
    case pb_fp_cmp_op_pb_lt_pb_register:
      flag = fpregs[instr->dr.dest] < fpregs[instr->dr.reg];
      break;
    case pb_fp_cmp_op_pb_le_pb_register:
      flag = fpregs[instr->dr.dest] <= fpregs[instr->dr.reg];
      break;
    case pb_rev_op_pb_int16:
      regs[instr->dr.dest] = ((uptr)((iptr)(regs[instr->dr.reg] << 56) >> 48)
                              | ((regs[instr->dr.reg] & 0xFF00) >> 8));
      break;
    case pb_rev_op_pb_uint16:
      regs[instr->dr.dest] = (((regs[instr->dr.reg] & 0x00FF) << 8)
                              | ((regs[instr->dr.reg] & 0xFF00) >> 8));
      break;
    case pb_rev_op_pb_int32:
      regs[instr->dr.dest] = ((uptr)((iptr)(regs[instr->dr.reg] << 56) >> 32)
                              | ((regs[instr->dr.reg] & (uptr)0xFF000000) >> 24)
                              | ((regs[instr->dr.reg] & (uptr)0x00FF0000) >> 8)
                              | ((regs[instr->dr.reg] & (uptr)0x0000FF00) << 8));
      break;
    case pb_rev_op_pb_uint32:
      regs[instr->dr.dest] = (((regs[instr->dr.reg] * (uptr)0x000000FF) << 24)
                              | ((regs[instr->dr.reg] & (uptr)0xFF000000) >> 24)
                              | ((regs[instr->dr.reg] & (uptr)0x00FF0000) >> 8)
                              | ((regs[instr->dr.reg] & (uptr)0x0000FF00) << 8));
      break;
    case pb_rev_op_pb_int64:
      regs[instr->dr.dest] = (((regs[instr->dr.reg] * (uptr)0x00000000000000FF) << 56)
                              | ((regs[instr->dr.reg] & (uptr)0x000000000000FF00) << 40)
                              | ((regs[instr->dr.reg] & (uptr)0x0000000000FF0000) << 24)
                              | ((regs[instr->dr.reg] & (uptr)0x00000000FF000000) << 8)
                              | ((regs[instr->dr.reg] & (uptr)0x000000FF00000000) >> 8)
                              | ((regs[instr->dr.reg] & (uptr)0x0000FF0000000000) >> 24)
                              | ((regs[instr->dr.reg] & (uptr)0x00FF000000000000) >> 40)
                              | ((regs[instr->dr.reg] & (uptr)0xFF00000000000000) >> 56));
      break;
    case pb_ld_op_pb_int8_pb_register:
      regs[instr->drr.dest] = *(signed char *)(regs[instr->drr.reg1] + regs[instr->drr.reg2]);
      break;
    case pb_ld_op_pb_int8_pb_immediate:
      regs[instr->dri.dest] = *(signed char *)(regs[instr->dri.reg] + regs[instr->dri.imm]);
      break;
    case pb_ld_op_pb_uint8_pb_register:
      regs[instr->drr.dest] = *(unsigned char *)(regs[instr->drr.reg1] + regs[instr->drr.reg2]);
      break;
    case pb_ld_op_pb_uint8_pb_immediate:
      regs[instr->dri.dest] = *(unsigned char *)(regs[instr->dri.reg] + regs[instr->dri.imm]);
      break;
    case pb_ld_op_pb_int16_pb_register:
      regs[instr->drr.dest] = *(signed short *)(regs[instr->drr.reg1] + regs[instr->drr.reg2]);
      break;
    case pb_ld_op_pb_int16_pb_immediate:
      regs[instr->dri.dest] = *(signed short *)(regs[instr->dri.reg] + regs[instr->dri.imm]);
      break;
    case pb_ld_op_pb_uint16_pb_register:
      regs[instr->drr.dest] = *(unsigned short *)(regs[instr->drr.reg1] + regs[instr->drr.reg2]);
      break;
    case pb_ld_op_pb_uint16_pb_immediate:
      regs[instr->dri.dest] = *(unsigned short *)(regs[instr->dri.reg] + regs[instr->dri.imm]);
      break;
    case pb_ld_op_pb_int32_pb_register:
      regs[instr->drr.dest] = *(signed int *)(regs[instr->drr.reg1] + regs[instr->drr.reg2]);
      break;
    case pb_ld_op_pb_int32_pb_immediate:
      regs[instr->dri.dest] = *(signed int *)(regs[instr->dri.reg] + regs[instr->dri.imm]);
      break;
    case pb_ld_op_pb_uint32_pb_register:
      regs[instr->drr.dest] = *(unsigned int *)(regs[instr->drr.reg1] + regs[instr->drr.reg2]);
      break;
    case pb_ld_op_pb_uint32_pb_immediate:
      regs[instr->dri.dest] = *(unsigned int *)(regs[instr->dri.reg] + regs[instr->dri.imm]);
      break;
    case pb_ld_op_pb_int64_pb_register:
      regs[instr->drr.dest] = *(uptr *)(regs[instr->drr.reg1] + regs[instr->drr.reg2]);
      break;
    case pb_ld_op_pb_int64_pb_immediate:
      regs[instr->dri.dest] = *(uptr *)(regs[instr->dri.reg] + regs[instr->dri.imm]);
      break;
    case pb_ld_op_pb_double_pb_register:
      memcpy(&fpregs[instr->drr.dest], (double *)(regs[instr->drr.reg1] + regs[instr->drr.reg2]), sizeof(double));
      break;
    case pb_ld_op_pb_double_pb_immediate:
      memcpy(&fpregs[instr->dri.dest], (double *)(regs[instr->dri.reg] + regs[instr->dri.imm]), sizeof(double));
      break;
    case pb_ld_op_pb_single_pb_register:
      memcpy(&fpregs[instr->drr.dest], (float *)(regs[instr->drr.reg1] + regs[instr->drr.reg2]), sizeof(float)); /* little endian */
      break;
    case pb_ld_op_pb_single_pb_immediate:
      memcpy(&fpregs[instr->dri.dest], (float *)(regs[instr->dri.reg] + regs[instr->dri.imm]), sizeof(float)); /* little endian */
      break;
    case pb_st_op_pb_int8_pb_register:
      *(char *)(regs[instr->drr.reg1] + regs[instr->drr.reg2]) = (char)regs[instr->drr.dest];
      break;
    case pb_st_op_pb_int8_pb_immediate:
      *(char *)(regs[instr->dri.reg] + regs[instr->dri.imm]) = (char)regs[instr->dri.dest];
      break;
    case pb_st_op_pb_int16_pb_register:
      *(short *)(regs[instr->drr.reg1] + regs[instr->drr.reg2]) = (short)regs[instr->drr.dest];
      break;
    case pb_st_op_pb_int16_pb_immediate:
      *(short *)(regs[instr->dri.reg] + regs[instr->dri.imm]) = (short)regs[instr->dri.dest];
      break;
    case pb_st_op_pb_int32_pb_register:
      *(int *)(regs[instr->drr.reg1] + regs[instr->drr.reg2]) = (int)regs[instr->drr.dest];
      break;
    case pb_st_op_pb_int32_pb_immediate:
      *(int *)(regs[instr->dri.reg] + regs[instr->dri.imm]) = (int)regs[instr->dri.dest];
      break;
    case pb_st_op_pb_int64_pb_register:
      *(uptr *)(regs[instr->drr.reg1] + regs[instr->drr.reg2]) = regs[instr->drr.dest];
      break;
    case pb_st_op_pb_int64_pb_immediate:
      *(uptr *)(regs[instr->dri.reg] + regs[instr->dri.imm]) = regs[instr->dri.dest];
      break;
    case pb_b_op_pb_fals_pb_register:
      if (!flag)
        next = (instruction_t *)regs[instr->dr.reg];
      break;
    case pb_b_op_pb_fals_pb_immediate:
      if (!flag)
        next = (instruction_t *)((char *)next_instr + instr->di.imm);
      break;
    case pb_b_op_pb_true_pb_register:
      if (flag)
        next = (instruction_t *)regs[instr->dr.reg];
      break;
    case pb_b_op_pb_true_pb_immediate:
      if (flag)
        next = (instruction_t *)((char *)next_instr + instr->di.imm);
      break;
    case pb_b_op_pb_always_pb_register:
      next = (instruction_t *)regs[instr->dr.reg];
      break;
    case pb_bs_op_pb_register:
      next = *(instruction_t **)(regs[instr->dr.dest] + regs[instr->dr.reg]);
      break;
    case pb_bs_op_pb_immediate:
      next = *(instruction_t **)(regs[instr->di.dest] + instr->di.immed);
      break;
    case pb_call:
      ((void (*)())regs[instr->dr.dest])();
      break;
    case pb_ret:
      return;
    case pb_adr:
      rags[instr->di.dest] = (uptr)next_instr + instr->di.immed;
      return;
    }
    instr = next_instr;
  }
}
