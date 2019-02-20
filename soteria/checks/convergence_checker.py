from soteria.executor import Executor
from soteria.exceptions import ConvergenceError
from soteria.components.procedure import Procedure
from soteria.components.parameter import Parameter
from soteria.checks.specification_generator import SpecificationGenerator
import logging

class ConvergenceChecker:

    CURRENT = 'current'
    OLD = 'old'
    IN = 'in'
    ITER = 'iter'

    def check(self, spec):
        for proc in spec.procedures:
            logging.info('Checking monotonicity for procedure ' + proc.name)
            self.check_monotonicity(spec, proc)
        logging.info('Checking LUB properties of ' + spec.merge.name + 'procedure')
        self.check_lub(spec)
        return True

    def check_monotonicity(self, spec, procedure):
        #preface + procedure + monotonicity check
        #monotonicty check = call procedure, assert current >= old
        parameter_names = self.get_replaced_parameters(spec.gteq.parameters, self.CURRENT, self.OLD) 
        monotonicity_expr = spec.gteq.name + '(' + ','.join(parameter_names) + ')'
        monotonicity_checks = []
        monotonicity_checks.append('ensures ' + monotonicity_expr + ';')
        
        generator = SpecificationGenerator()
        specification_text = spec.preface + '\n' + generator.generate_spec('monotonicity', monotonicity_checks, [], procedure)
        try:
            message = Executor.execute_boogie([procedure], specification_text, 'monotonicity_' + procedure.name)
        except Exception as e:
            raise ConvergenceError(e)
        return True

    def check_lub(self, spec):
        #preface + merge + join check
        #join check = call procedure, assert LUB properties
        #LUB properties = result >= both, no other state >= both but < result
        checks = []
        
        checks.append('ensures (' + spec.gteq.name + '(' + ','.join(self.get_replaced_parameters(spec.gteq.parameters, self.CURRENT, self.OLD)) + '));')
        checks.append('ensures (' + spec.gteq.name + '(' + ','.join(self.get_replaced_parameters(spec.gteq.parameters, self.CURRENT, self.IN)) + '));')

        iteratives = self.get_iterative_var_on_datatypes(spec.variables)
        iteration_gteq_old = spec.gteq.name + '(' + ','.join(self.get_replaced_parameters(spec.gteq.parameters, self.ITER, self.OLD)) + ')'
        iteration_gteq_in = spec.gteq.name + '(' + ','.join(self.get_replaced_parameters(spec.gteq.parameters, self.ITER, self.IN)) + ')'
        iteration_gteq_current = spec.gteq.name + '(' + ','.join(self.get_replaced_parameters(spec.gteq.parameters, self.ITER, self.CURRENT)) + ')'
        checks.append('ensures (forall ' + ', '.join(iteratives) + '::' + iteration_gteq_old + ' && ' + iteration_gteq_in + ' ==> ' + iteration_gteq_current + ');')

        # calling_procedure = 'procedure lub_' + spec.merge.name + '()\n' + 'modifies ' + ', '.join(spec.merge.modifies) + ';\n' + '\n'.join(checks) + '\n{\n' + 'call ' + spec.merge.name + '(' + ', '.join([p.name for p in constants]) + ');\n}'
        
        generator = SpecificationGenerator()
        specification_text = spec.preface + '\n' + generator.generate_spec('lub', checks, [], spec.merge)
        try:
            message = Executor.execute_boogie([spec.merge], specification_text, 'lub_' + spec.merge.name)
        except Exception as e:
            raise ConvergenceError(e)
        return True

    def get_iterative_var_on_datatypes(self, variables):
        result = []
        for each in variables:
            result.append('_' + each.name + ':' + each.datatype)
        return result

    def get_replaced_parameters(self, parameters, lhs, rhs):
        result = []
        for each in parameters:
            if each.name.endswith('1'):
                result.append(self.get_modified(each.name, lhs))
            else:
                result.append(self.get_modified(each.name, rhs))
        return result

    def get_modified(self, name, category):
        if category == self.CURRENT:
            return name[:-1]
        if category == self.OLD:
            return 'old(' + name[:-1] + ')'
        if category == self.IN:
            return '_' + name[:-1] + '1'
        if category == self.ITER:
            return '_' + name[:-1]