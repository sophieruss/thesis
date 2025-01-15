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

class Sw:
    def __init__(self, src, dest):
        self.src = src
        self.dest = dest
    
class Lw_U:
    def __init__(self, src, dest):
        self.src = src
        self.dest = dest
        
class Lw_T:
    def __init__(self, src, dest):
        self.src = src
        self.dest = dest
        
class Get:
    def __init__(self, dest):
        self.dest = dest

class Put:
    def __init__(self, src):
        self.src = src
        
class trustedMode:
    def __init__(self):
        pass
    
class untrustedMode:
    def __init__(self):
        pass
    
class alert:
    def __init__(self):
        pass
    
class returnn:
    def __init__(self):
        pass
