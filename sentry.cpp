#include <iostream>
#include <unordered_map>
#include <variant>
#include "commands.h"

int n;                                      // naturals
int pc = 0;                                 // program counter
int r[32] = {0};                            // registers r -> X         
int R[32] = {0};                            // register file r -> Z

int hash(int z){
    return (z * 31) ^ (z >> 16);
}

std::unordered_map<int, int> M;             // hash storage Z -> Z

using commands = std::variant<add, addi, sub, jump, bgtz>;
std::unordered_map<int, commands> program;


void fun_add(int dest, int src, int temp){
    add cmd = {dest, src, temp};
    program[pc] = cmd;
    int n_0 = R[src];
    int n_1 = R[temp];
    int n_2 = n_0 + n_1;
    
    R[dest] = n_2;
    pc++;
}

void fun_addi(int dest, int src, int n_1){
    addi cmd = {dest, src, n_1};
    program[pc] = cmd;
    int n_0 = R[src];
    int n_2 = n_0 + n_1;

    R[dest] = n_2;
    pc++;
}

void fun_sub(int dest, int src, int temp){
    sub cmd = {dest, src, temp};
    program[pc] = cmd;
    int n_0 = R[src];
    int n_1 = R[temp];
    int n_2 = n_0 - n_1;

    R[dest] = n_2;
    pc++;
}

void fun_jump(int n){
    jump cmd = {n};
    program[pc] = cmd;

    pc = n;
}

void fun_bgtz_g(int src, int n){
    bgtz cmd = {src, n};
    program[pc] = cmd;
    int n_1 = R[src];
    
    if (n_1 > 0) {
        pc = n;
    }
    else {};
}

void fun_bgtz_l(int src, int n){
    bgtz cmd = {src, n};
    program[pc] = cmd;
    int n_1 = R[src];

    if (n_1 <= 0) {
        pc++;
    }
    else {};
}

void print_program() {
    std::cout << "Program: " << std::endl;
    std::cout << "pc: " << pc << std::endl;
    std::cout << "r[]: ";
    for (int i = 0; i < 32; ++i) {
        std::cout << r[i] << " ";
    }
    std::cout << std::endl;

    std::cout << "R[]: ";
    for (int i = 0; i < 32; ++i) {
        std::cout << R[i] << " ";
    }
    std::cout << std::endl;
    std::cout << "\n" << std::endl;
}


int main() {
    std::cout << "hello sentry" << std::endl;

    R[1] = 1;
    R[2] = 2;
    R[3] = 3;
    print_program();

    fun_add(1, 2, 3);

    print_program();

    return 0;
}
// int main(){
    // fun_add(1, 2, 3);
    // fun_addi(1, 2, 3);
    // fun_sub(1, 2, 3);
    // fun_jump(1);
    // fun_bgtz_g(1, 2);
    // fun_bgtz_l(1, 2);
    // return 0;
// }