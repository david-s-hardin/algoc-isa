// Copyright (C) 2019, David S. Hardin
// License: A 3-clause BSD license.  See the LICENSE file in this directory.

// LEG64 ISA

#include <iostream>
#include <ac_int.h>
#include <rac.h>
using namespace std;

typedef unsigned long uint64; // Just used to facilitate printing

// RAC begin

typedef ac_int<1,false> ui1;
typedef ac_int<8,false> ui8;
typedef ac_int<10,false> ui10;
typedef ac_int<12,false> ui12;
typedef ac_int<32,false> ui32;
typedef ac_int<64,false> ui64;

//#define BIG_STRUCT

#ifdef BIG_STRUCT
#define RTYP void
#define RVAL 
#define amp(x) &x
#define RASN
#else
#define RTYP BSTObj
#define RVAL Obj
#define amp(x) x
#define RASN Obj =
#endif

enum leg64regType {PC, SP, REG, DMEM, CMEM};

//             0    1    2     3    4     5    6    7     8      9    10   11
enum leg64ops {BAD, NOP, HALT, ADD, ADDI, ASR, CMP, CMPI, CONST, LSL, LSR, MUL,
//             12   13    14   15   16 17   18   19   20   21
               SUB, SUBI, LDR, STR, B, BEQ, BHI, BHS, BLO, BLS,
//             22   23   24
               BMI, BNE, BPL};


#define REG_SZ 256

#define DMEM_SZ 4096
#define CMEM_SZ 1024

// leg64 machine state

struct leg64St {
  ui10 pc;
  ui12 sp;
  array<ui64, REG_SZ>regs;
  array<ui64, DMEM_SZ>dmem;
  array<ui32, CMEM_SZ>cmem;
  // struct leg64inst ins;    // current decoded instruction
  ui8 opcode;               // current decoded instruction
  ui8 op1;
  ui8 op2;
  ui8 op3;
  ui1 C;                    // Carry Status Flag
  ui1 N;                    // Negative Status Flag
  ui1 Z;                    // Zero Status Flag
  ui1 V;                    // oVerflow Status Flag
  // ui64 insCount;
  //  ui8 err;                  // leg64 machine error code
};
