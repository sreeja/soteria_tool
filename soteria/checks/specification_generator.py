from soteria.components.parameter import Parameter
import re

class SpecificationGenerator:
    def generate_spec(self, test_name, ensures, assumptions, procedure):
        testing_procedure = procedure.get_signature() + '\n{\n' + procedure.implementation + '\n}'

        constants = self.get_constants(procedure.parameters, '_')
        constant_declarations = self.generate_const_text(constants)

        for each in procedure.requires:
            condition = each
            for p in procedure.parameters:
                condition = re.sub(p.name, '_'+p.name, condition)
            assumptions.append('assume ' + condition + ';')

        calling_procedure = 'procedure ' + test_name + '_' + procedure.name + '()\n' + 'modifies ' + ', '.join(procedure.modifies) + ';\n' + '\n'.join(ensures) + '\n{\n' + '\n'.join(assumptions) + '\ncall ' + procedure.name + '(' + ', '.join([p.name for p in constants]) + ');\nassume {:captureState "after"} true;\n}'

        return testing_procedure + '\n' + constant_declarations + '\n' + calling_procedure

    def get_constants(self, parameters, prefix = '', suffix = ''):
        constants = []
        for each in parameters:
            constants.append(Parameter(prefix+each.name+suffix, each.datatype))
        return constants

    def generate_const_text(self, constants):
        lines = []
        for each in constants:
            lines.append('const ' + each.name + ':' + each.datatype + ';')
        return '\n'.join(lines)

    def get_substituted_const(self, expr, p):
        return re.sub(p.name, '_'+p.name, expr)