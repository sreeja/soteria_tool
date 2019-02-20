from soteria.components.specification import Specification
from soteria.components.variable import Variable
from soteria.components.function import Function
from soteria.components.parameter import Parameter
from soteria.components.procedure import Procedure
import re

class Parser:
    def parse(self, spec_name, spec_text):
        specification = Specification(spec_name)
        import ipdb
        preface = []
        procedure_lines = []
        for i, line in enumerate(spec_text):
            if line.strip().startswith('@invariant'):
                invariant = self.extract_function(spec_text[i+1:], i+2)
                specification.set_invariant(invariant)
            if line.strip().startswith('@gteq'):
                gteq = self.extract_function(spec_text[i+1:], i+2)
                specification.set_gteq(gteq)
            if line.strip().startswith('@merge'):
                end = self.get_end(spec_text[i+1:], i+1)
                procedure_lines = procedure_lines + list(range(i+1, end + 1))
                merge = self.extract_procedure(spec_text[i+1:end + 1], i+1)
                specification.set_merge(merge)
            if line.strip().startswith('procedure ') and not spec_text[i-1].startswith('@merge'):
                end = self.get_end(spec_text[i:], i)
                procedure_lines = procedure_lines + list(range(i, end + 1))
                procedure = self.extract_procedure(spec_text[i:end + 1], i)
                specification.add_procedure(procedure)
            if line.strip().startswith('@'):
                preface.append('//' + line)
            elif i in procedure_lines:
                preface.append('//' + line)
            else:
                preface.append(line)
            if line.strip().startswith('var ') and i not in procedure_lines:
                variable = self.extract_variable(spec_text[i:], i + 1)
                specification.add_variable(variable)
        specification.set_preface(''.join(preface))
        return specification

    def extract_variable(self, spec, position):
        spec_text = ''.join(spec)
        var_text = spec_text[spec_text.index('var')+3 : spec_text.index(';')].strip()
        var_name = var_text[:var_text.index(':')].strip()
        var_type = var_text[var_text.index(':')+1:].strip()
        return Variable(var_name, var_type, position)

    def get_end(self, spec, i):
        count = 0
        for j, line in enumerate(spec):
            if '{' in line and (('//' not in line) or line.index('//') > line.index('}')):
                count = count + 1
            if '}' in line and (('//' not in line) or line.index('//') > line.index('}')):
                if count > 1:
                    count = count - 1
                else:
                    return i + j

    def extract_function(self, spec, position):
        spec_text = ''.join(spec)
        semi_colon_index = spec_text.index(';')
        bracket_index = spec_text.index('{')
        function_end = min(semi_colon_index, bracket_index)
        function_text = spec_text[:function_end].strip()
        fun_name = function_text[9:function_text.index('(')].strip()
        function = Function(fun_name, position)
        param_spec = function_text[function_text.index('(') + 1 : function_text.index(')')].strip()
        for each in self.__get_params(param_spec):
            function.add_param(each)
        returndt = self.__get_returndt(function_text)
        function.set_return(returndt)
        if bracket_index > 1:
            implementation = spec_text[bracket_index+1:spec_text.index('}')].strip()
            function.implementation = implementation
        return function

    def __get_params(self, param_spec):
        if not param_spec.strip():
            return []
        params = []
        for each in param_spec.split(','):
            p_name = each[:each.index(':')].strip()
            p_type = each[each.index(':') + 1 :].strip()
            param = Parameter(p_name, p_type)
            params.append(param)
        return params

    def __get_returndt(self, body):
        p = re.compile('return')
        m = p.search(body).start()
        return_substr = body[m+7:].split('\n')[0].replace('(', '').replace(')','')
        if ':' in return_substr:
            return_substr = return_substr[return_substr.index(':')+1:]
        return return_substr

    def extract_procedure(self, procedure_lines, position):
        proc_text = ''.join(procedure_lines)
        name = proc_text[10:proc_text.index('(')].strip()
        procedure = Procedure(name, position)
        param_spec = proc_text[proc_text.index('(') + 1 : proc_text.index(')')].strip()
        for param in self.__get_params(param_spec):
            procedure.add_parameter(param)
        procedure.set_implementation(proc_text[proc_text.index('{') + 1 : proc_text.rindex('}')].strip())
        for line in procedure_lines:
            if '{' in line:
                break
            elif line.strip().startswith('modifies'):
                modifies_sub = line[line.index('modifies'):]
                modifies_exp = modifies_sub[8:modifies_sub.index(';')].strip()
                for m in modifies_exp.split(','):
                    procedure.add_modifies(m.strip())
            elif line.strip().startswith('ensures'):
                ensures_sub = line[line.index('ensures'):]
                ensures_exp = ensures_sub[8:ensures_sub.index(';')].strip()
                procedure.add_ensures(ensures_exp)
            elif line.strip().startswith('requires'):
                requires_sub = line[line.index('requires'):]
                requires_exp = requires_sub[8:requires_sub.index(';')].strip()
                procedure.add_requires(requires_exp)
        return procedure