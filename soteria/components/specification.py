class Specification:
    '''
    This class is the object which holds the specification structure
    '''
    def __init__(self, name):
        self.name = name
        self.variables = []
        self.invariant = ''
        self.preface = ''
        self.procedures = []
        self.merge = ''
        self.gteq = ''

    def add_variable(self, variable):
        self.variables.append(variable)

    def set_preface(self, preface):
        self.preface = preface

    def set_invariant(self, inv_func):
        self.invariant = inv_func

    def add_procedure(self, procedure):
        self.procedures.append(procedure)

    def set_merge(self, merge_name):
        self.merge = merge_name

    def set_gteq(self, ge_func):
        self.gteq = ge_func

    # def get_global_var(self, var):
    #     for v in self.variables:
    #         if v.name == var:
    #             return v