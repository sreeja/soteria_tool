class Function:
    '''
    This class defines the structure of an function
    '''
    def __init__(self, name, position):
        self.name = name
        self.parameters = []
        self.position = position
        self.implementation = ''

    def add_param(self, parameter):
        self.parameters.append(parameter)

    def set_return(self, datatype):
        self.returndt = datatype

    def __eq__(self, other):
        if self.name == other.name and self.position == other.position and self.parameters == other.parameters:
            return True
        return False