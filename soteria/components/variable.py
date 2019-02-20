class Variable:
    '''
    This holds a global variables defined in the specificaiton
    ''' 
    def __init__(self, name, datatype, position):
        self.name = name
        self.datatype = datatype
        self.position = position

    def __eq__(self, other):
        if self.name == other.name and self.datatype == other.datatype and self.position == other.position:
            return True
        return False

