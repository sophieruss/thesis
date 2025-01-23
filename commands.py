class Add:
    def __init__(self, dest, src, temp):
        self.command = "add"
        self.dest = dest
        self.src = src
        self.temp = temp

class Addi:
    def __init__(self, dest, src, n_1):
        self.command = "addi"
        self.dest = dest
        self.src = src
        self.n_1 = n_1

class Sub:
    def __init__(self, dest, src, temp):
        self.commands = "sub"
        self.dest = dest
        self.src = src
        self.temp = temp

class Jump:
    def __init__(self, n):
        self.command = "jump"
        self.n = n

class Bgtz:
    def __init__(self, src, n):
        self.command = "bgtz"
        self.src = src
        self.n = n

class Sw:
    def __init__(self, src, dest):
        self.command = "sw"
        self.src = src
        self.dest = dest
    
class Lw_U:
    def __init__(self, src, dest):
        self.command = "lw_U"
        self.src = src
        self.dest = dest
        
class Lw_T:
    def __init__(self, src, dest):
        self.command = "lw_T"
        self.src = src
        self.dest = dest
        
class Get:
    def __init__(self, dest):
        self.command = "get"
        self.dest = dest

class Put:
    def __init__(self, src):
        self.command = "put"
        self.src = src
        
class trustedMode:
    def __init__(self):
        self.command = "trustedMode"
        pass
    
class untrustedMode:
    def __init__(self):
        self.command = "untrustedMode"
        pass
    
class alert:
    def __init__(self):
        self.command = "alert"
        pass
    
class returnn:
    def __init__(self):
        self.command = "returnn"
        pass


# accept, reject, empty