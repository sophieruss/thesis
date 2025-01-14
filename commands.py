class Add:
    def __init__(self, dest, src, temp):
        self.dest = dest
        self.src = src
        self.temp = temp

class Addi:
    def __init__(self, dest, src, n_1):
        self.dest = dest
        self.src = src
        self.n_1 = n_1

class Sub:
    def __init__(self, dest, src, temp):
        self.dest = dest
        self.src = src
        self.temp = temp

class Jump:
    def __init__(self, n):
        self.n = n

class Bgtz:
    def __init__(self, src, n):
        self.src = src
        self.n = n
