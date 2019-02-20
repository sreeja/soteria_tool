class Procedure:
    '''
    This models a procedure definition and implementation
    '''        
    def __init__(self, name, position):
        self.name = name
        self.parameters = []
        self.modifies = []
        self.ensures = []
        self.requires = []
        self.implementation = ''
        self.position = position
        #self.signature = ''

    def add_parameter(self, parameter):
        self.parameters.append(parameter)

    def add_modifies(self, modifies):
        self.modifies.append(modifies)

    def add_ensures(self, condition):
        self.ensures.append(condition)

    def add_requires(self, condition):
        self.requires.append(condition)

    def get_signature(self):
        parameter_list = []
        for p in self.parameters:
            parameter_list.append(p.name + ':' + p.datatype)
        signature = 'procedure ' + self.name + '(' + ', '.join(parameter_list) + ')\n'
        signature = signature + 'modifies ' + ', '.join(self.modifies) + ';\n'
        for r in self.requires:
            signature = signature + 'requires (' + r + ');\n'
        for e in self.ensures:
            signature = signature + 'ensures (' + e + ');\n'
        return signature

    def set_implementation(self, code):
        self.implementation = code

    def __eq__(self, other):
        if self.name == other.name and self.parameters == other.parameters and self.position == other.position:
            return True
        return False

    def get_related_param(self, var_type):
        related_params = [param for param in self.parameters if param.datatype == var_type]
        # if len(related_params) > 1:
        #     raise Exception("Not able to resolve the corresponding global variable for parameter")
        if len(related_params) == 0:
            raise Exception("Merge operation does not specify an incoming state to be merged")
        return related_params[0]
