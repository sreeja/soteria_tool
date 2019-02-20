class Parameter:
    '''
    This holds function/procedure parameters defined in the specificaiton
    ''' 
    def __init__(self, name, datatype):
        self.name = name
        self.datatype = datatype
 
    def __eq__(self, other):
        if self.name == other.name and self.datatype == other.datatype:
            return True
        return False
