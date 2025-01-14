#include <iostream>
#include <unordered_map>

int n;                                      // naturals
int pc = 0;                                 // program counter        (why is this not a r15)
int r[32] = {0};                            // registers r -> X         
int R[32] = {0};                            // register file r -> Z
std::unordered_map<int, int> M;             // memory
int S = 0;                                  // mode bit

// what is the best way to represent registers. 
// should they be their own data type?
// does it even matter?  what does it need to store? whether in use?

struct add {
    int r_d;
    int r_s;
    int r_t;
};

struct addi {
    int r_d;
    int r_s;
    int n;
};

struct sub {
    int r_d;
    int r_s;
    int r_t;
};

struct jump {
    int addr;
};

struct bgtz {
    int r_s;
    int addr;
};

using commands = std::variant<add, addi, sub, jump, bgtz>;

std::unordered_map<int, commands> program;

void fun_add(int dest, int src, int temp){
    add cmd = {dest, src, temp};
    program[pc] = cmd;
    int n_0 = R[src];
    int n_1 = R[temp];
    int n_2 = n_0 + n_1;
    if (S == 1) {
        R[dest] = n_2;
        pc = pc++;
    } 
    else {}
}

void fun_addi(int dest, int src, int n_1){
    addi cmd = {dest, src, n_1};
    program[pc] = cmd;
    int n_0 = R[src];
    int n_2 = n_0 + n_1;
    if (S == 1) {
        R[dest] = n_2;
        pc = pc++;
    } 
    else {}
}

void fun_sub(int dest, int src, int temp){
    sub cmd = {dest, src, temp};
    program[pc] = cmd;
    int n_0 = R[src];
    int n_1 = R[temp];
    int n_2 = n_0 - n_1;
    if (S == 1) {
        R[dest] = n_2;
        pc = pc++;
    }
    else {}
}

void fun_jump(int addr){
    jump cmd = {addr};
    program[pc] = cmd;
    if (S == 1) {
        pc = addr;
    }
    else {}
}

void fun_bgtz_g(int src, int addr){
    bgtz cmd = {src, addr};
    program[pc] = cmd;
    int n_1 = R[src];
    if (S==1 && n_1 > 0) {
        pc = addr;
    }
    else {};
}

void fun_bgtz_l(int src, int addr){
    bgtz cmd = {src, addr};
    program[pc] = cmd;
    int n_1 = R[src];
    if (S==1 && n_1 <= 0) {
        pc++;
    }
    else {};
}

