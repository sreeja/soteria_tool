from soteria.checks.safety_checker import SafetyChecker
from soteria.debug_support.debugger import Debugger
from soteria.executor import Executor
import itertools

class Token:
    def __init__(self, op):
        self.operation_name = op
        self.merges = []
        self.operations_shared = {}

    def add_operation(self, op, tokens):
        self.operations_shared[op] = tokens

    def add_merge(self, merge):
        self.merges.append(merge)

    def get_merges_text(self):
        return ' and '.join(self.merges)

    def get_operations_text(self):
        return ' and '.join([str(key) + ' on ' + str(value) for key, value in self.operations_shared.items()])


class TokenGenerator:
    def convert_to_text(self, tokens):
        text = []
        for key, value in tokens.items():
            text.append(value.operation_name + ':')
            text.append(value.get_merges_text() + ' should be executed while acquiring the token.')
            text.append('Token shared with ' + value.get_operations_text() + '\n')
        return '\n'.join(text)
    
    def generate_tokens(self, specification, pairs):
        tokens = {}
        for each in pairs:
            if each[1].name not in tokens.keys():
                tokens[each[1].name] = Token(each[1].name)
            if each[0] in specification.merges:
                tokens[each[1].name].add_merge(each[0].name)
            else:
                suggestions = self.get_token_suggestions(specification, each)
                tokens[each[1].name].add_operation(each[0].name, suggestions)
        return tokens

    def get_token_suggestions(self, specification, pair):
        #the pair here is the one which failed stability test
        tokens = []
        debugger = Debugger()
        params = debugger.get_parameters(pair)
        name = 'stability_' + pair[0].name + '_' + pair[1].name
        models = debugger.get_models('results/' + name + '.model')
        for m in models:
            param_values = {}
            for p in params:
                derivations = debugger.get_derivations(p, list(m.keys()))
                for each in derivations:
                    if m[each] not in param_values.keys():
                        param_values[m[each]] = []
                    param_values[m[each]].append(each)
            multiple_value_params = []
            for each in param_values.keys():
                if len(param_values[each]) == 2:
                    multiple_value_params.append(param_values[each][0] + ' != ' + param_values[each][1])
                elif len(param_values[each]) > 2:
                    raise Exception('Check this case.. The parameters with value ' + each + ' is ' + len(param_values[each]))
            for i in range(0, len(multiple_value_params)):
                for each in itertools.combinations(multiple_value_params, i+1):
                    checker = SafetyChecker()
                    verification_condition = checker.generate_stability_check(specification, pair, list(each))
                    if self.check_with_restrictions(pair, verification_condition, name):
                        tokens.append(' && '.join(each))
        return tokens

    def check_with_restrictions(self, pair, verification_condition, name):
        try:
            message = Executor.execute_boogie([pair[0], pair[1]], verification_condition, name)
        except Exception as e:
            return False
        return True