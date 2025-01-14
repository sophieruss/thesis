#ifndef commands_h   
#define commands_h
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

#endif 
