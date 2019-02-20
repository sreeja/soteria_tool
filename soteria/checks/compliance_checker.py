import itertools
from soteria.exceptions import ComplianceError

class ComplianceChecker:
    def check(self, spec):
        self.check_gteq(spec.gteq, spec.variables)
        self.check_invariant(spec.invariant, spec.variables)
        self.check_merge(spec.merge, spec.variables)

    def check_invariant(self, invariant, variables):
        ##- the no of function parameters == no of global variables
        ##- all global variables should have a function parameter with the same name
        ##- return value should be bool
        if not invariant:
            raise ComplianceError('No invariant defined!')
        
        if len(invariant.parameters) != len(variables):
            raise ComplianceError('The number of parameters of the invariant function and the number of global variables are not equal.')
        for var in variables:
            if not [x for x in invariant.parameters if x.name == var.name and x.datatype == var.datatype]:
                raise ComplianceError('The variable <' + var.name + '> does not have a corresponding parameter in the invariant')
        if invariant.returndt != 'bool':
            raise ComplianceError('The return value of teh invariant function must be bool')
        return True

    def check_gteq(self, gteq, variables):
        ##- all global variables should be present in greater than function
        ##- must have exactly pairs of parameters of the same datatype
        ##- must have return value bool
        ##- all variables must be named a1, a2, b1, b2 .....

        if not gteq:
            raise ComplianceError('No greater than or equal to defined!')

        if len(gteq.parameters) != len(variables) * 2:
            raise ComplianceError('The greater than or equal two function must contain a pair of all the variables defined')

        # if len(gteq.parameters) % 2 != 0:
        #     raise ComplianceError('The function ' + gteq.name + ' should have parameter pairs')
        if not self.__all_var_in_gteq(gteq, variables):
            raise ComplianceError('All global variables needs to be present in the greater than or equal to function defined')
        datatype_list = [x.datatype for x in gteq.parameters]
        non_pairs = [x for x in datatype_list if datatype_list.count(x) % 2 != 0]
        if len(non_pairs) != 0:
            raise ComplianceError('The function ' + gteq.name + ' should have a matching parameters for datatypes')
        if gteq.returndt != 'bool':
            raise ComplianceError('The function ' + gteq.name + ' should have return value of type bool')
        return True

    def check_merge(self, merge, variables):
        ##- no of parameters of merge == no of variables in modifies clause == no of variables declared
        ##- all modifies variable must have a parameter with the same datatype
        if not merge:
            raise ComplianceError('No merge procedures defined!')
        
        if len(merge.modifies) != len(variables):
            raise ComplianceError('All variables declared should be modified during merge')
        if len(merge.modifies) != len(merge.parameters):
            raise ComplianceError('The number of parameters of the merge operation ' + merge.name + ' should be equal to the number of variables it modifies')
        # if self.__multiple_params_with_same_type(merge):
        #     raise ComplianceError('There are more than one parameter with the same datatype in ' + merge.name)
        try:
            self.__each_modifies_has_param(merge, variables)
        except Exception as e:
            raise ComplianceError(str(e))
        return True

    def __all_var_in_gteq(self, gteq, variables):
        for var in variables:
            if not (var.datatype in [p.datatype for p in gteq.parameters]):
                return False
            if not (var.name + '1' in [p.name for p in gteq.parameters]):
                return False
            if not (var.name + '2' in [p.name for p in gteq.parameters]):
                return False
        return True

    def __each_modifies_has_param(self, proc, variables):
        for m in proc.modifies:
            var = self.__get_global_var(m, variables)
            try:
                param = proc.get_related_param(var.datatype)
            except Exception as e:
                raise e
        return True

    def __get_global_var(self, name, variables):
        for each in variables:
            if each.name == name:
                return each

    # def __multiple_params_with_same_type(self,proc):
    #     for each in itertools.combinations(proc.parameters, 2):
    #         if each[0].datatype == each[1].datatype:
    #             return True
    #     return False
