from soteria.debug_support.model_parser import ModelParser
from soteria.debug_support.boogie_output_parser import BoogieOutputParser
import re

class Debugger:
    def get_debug_info(self, operations, specification_text, test_result, model_file_path):
        if operations:
            params = self.get_parameters(operations)
            models = self.get_models(model_file_path)
        errors = self.get_failures(specification_text, test_result)
        result = []
        for err in errors:
            result.append(err.message)
            result.append(err.expression)
            for rl in err.related_locations:
                result.append(rl.message)
                result.append(rl.expression)
        if operations:
            result.append('The value of parameters and variables are ::')
            for m in models:
                for p in params:
                    derivations = self.get_derivations(p, list(m.keys()))
                    for each in derivations:
                        result.append(each + ' -> ' + m[each])
        return '\n'.join(result)


    def get_parameters(self, operations):
        params = set()
        for each in operations:
            for p in each.parameters:
                params.add(p.name)
        return params

    def get_failures(self, text, test_result):
        parser = BoogieOutputParser()
        errors = parser.parse(test_result)
        for err in errors:
            err.set_expression(text[err.line-1].strip())
            for rl in err.related_locations:
                rl.set_expression(text[rl.line-1].strip())
        return errors


    def get_models(self, model_file_path):
        model_file = open(model_file_path)
        model_text = ''.join(model_file.readlines())
        parser = ModelParser()
        models = parser.parse(model_text)
        return models

    def get_derivations(self, param, key_list):
        result = []
        if param in key_list:
            result.append(param)
        for k in key_list:
            m = re.search('^_' + param + '\d$', k)
            if m:
                result.append(k)
            n = re.search('^_' + param, k)
            if n:
                result.append(k)
        #return [x fox in keylist if x is param or re.search('^_' + param + '\d$', x)]
        return result
