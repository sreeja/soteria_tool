import itertools
import re
from soteria.executor import Executor
from soteria.exceptions import SafetyError 
import logging
from soteria.checks.specification_generator import SpecificationGenerator

class SafetyChecker:
    def check(self, spec):
        flag = True
        failed = []
        for proc in spec.procedures:
            logging.info('Checking whether ' + proc.name + ' upholds the invariant')
            try:
                self.check_safety(spec, proc)
            except Exception as e:
                logging.error(str(e))
                flag = False
        logging.info('Checking whether ' + spec.merge.name + ' upholds the invariant')
        try:
            self.check_safety(spec, spec.merge)
        except Exception as e:
            logging.error(str(e))
            flag = False
        # for pair in itertools.permutations(spec.procedures, 2): # + spec.merges, 2):
        #     try:
        #         logging.info('Checking whether ' + pair[0].name + ' and ' + pair[1].name + ' are stable under each other')
        #         self.check_pair_stability(spec, pair)
        #     except Exception as e:
        #         logging.error(str(e))
        #         flag = False
        #         failed.append((pair[0], pair[1]))
        for each in spec.procedures: # + spec.merge:
            # try:
            #     logging.info('Checking whether ' + each.name + ' is stable under itself')
            #     self.check_pair_stability(spec, [each, each])
            # except Exception as e:
            #     logging.error(str(e))
            #     flag = False
            #     failed.append(each)
            try:
                logging.info('Checking whether ' + each.name + ' upholds the precondition of merge')
                self.check_stability(spec, each)
            except Exception as e:
                logging.error(str(e))
                flag = False
                failed.append((each, spec.merge))
            # try:
            #     logging.info('Checking whether merge upholds the precondition of ' + each.name)
            #     self.check_stability_under_merge(spec, each)
            # except Exception as e:
            #     logging.error(str(e))
            #     flag = False
            #     failed.append((spec.merge, each))
        logging.info('Checking whether ' + spec.merge.name + ' upholds the precondition of itself')
        try:
            self.check_stability_merge(spec)
        except Exception as e:
            logging.error(str(e))
            flag = False
            failed.append(spec.merge)
        return flag, failed

    def check_safety(self, spec, procedure):
        #preface + procedure + safety check
        #safety check = assume inv, call procedure, assert inv 
        invariant_text = spec.invariant.name + '(' + ','.join(param.name for param in spec.invariant.parameters) + ')'
        safety_checks = []
        safety_checks.append('ensures ' + spec.invariant.implementation + ';')
        safety_assumptions = []
        safety_assumptions.append('assume ' + invariant_text + ';')
        if procedure.name == spec.merge.name:
            safety_assumptions.append('assume ' + self.get_invariant_incoming_state(spec) + ';')
        
        generator = SpecificationGenerator()
        specification_text = spec.preface + '\n' + generator.generate_spec('safety', safety_checks, safety_assumptions, procedure)
        try:
            message = Executor.execute_boogie([procedure], specification_text, 'safety_' + procedure.name)
        except Exception as e:
            raise SafetyError(e)
        return True

    def get_invariant_incoming_state(self, spec):
        return spec.invariant.name + '(' + ','.join('_'+param.name+'1' for param in spec.invariant.parameters) + ')'


    # def get_modified_merge_inv(self, spec):
    #     modified = spec.merge.requires[:]
    #     for each in spec.variables:
    #         old = re.compile(r'\b' + each.name + r'\b')
    #         new = re.compile(r'\b' + each.name + '1' + r'\b')
    #         for i in range(len(modified)):
    #             modified[i] = old.sub('old(' + each.name + ')', modified[i])
    #             modified[i] = new.sub(each.name, modified[i])
    #     return modified

    def check_stability(self, spec, procedure):
        invariant_text = spec.invariant.name + '(' + ','.join(param.name for param in spec.invariant.parameters) + ')'
        invariant_text = invariant_text + ' && ' + spec.invariant.name + '(' + ','.join(param.name + '1' for param in spec.invariant.parameters) + ')'
        stability_checks = []
        for each in spec.merge.requires:
            stability_checks.append('ensures ' + each + ';')
        stability_assumptions = []
        stability_assumptions.append('assume ' + invariant_text + ';')
        for each in spec.merge.requires:
            stability_assumptions.append('assume ' + each + ';')
        
        generator = SpecificationGenerator()
        merge_constants = generator.get_constants(spec.merge.parameters)
        merge_constants_declarations = generator.generate_const_text(merge_constants)
        specification_text = spec.preface + '\n' + merge_constants_declarations + '\n' + generator.generate_spec('stability', stability_checks, stability_assumptions, procedure)
        try:
            message = Executor.execute_boogie([procedure], specification_text, 'stability_' + procedure.name)
        except Exception as e:
            raise SafetyError(e)
        return True

    def check_stability_under_merge(self, spec, procedure):
        invariant_text = spec.invariant.name + '(' + ','.join(param.name for param in spec.invariant.parameters) + ')'
        invariant_text = invariant_text + ' && ' + spec.invariant.name + '(' + ','.join('_' + param.name + '1' for param in spec.invariant.parameters) + ')'
        stability_checks = []
        if procedure.requires:
            stability_checks.append('ensures ' + ' && '.join(procedure.requires) + ';')
        stability_assumptions = []
        stability_assumptions.append('assume ' + invariant_text + ';')
        if procedure.requires:
            stability_assumptions.append('assume ' + ' && '.join(procedure.requires) + ';')
        
        generator = SpecificationGenerator()
        proc_constants = generator.get_constants(procedure.parameters)
        proc_constants_declarations = generator.generate_const_text(proc_constants)
        specification_text = spec.preface + '\n' + proc_constants_declarations + '\n' + generator.generate_spec('stability', stability_checks, stability_assumptions, spec.merge)
        try:
            message = Executor.execute_boogie([procedure], specification_text, 'stability_merge_under_' + procedure.name)
        except Exception as e:
            raise SafetyError(e)
        return True

    def check_pair_stability(self, spec, pair):
        invariant_text = spec.invariant.name + '(' + ','.join(param.name for param in spec.invariant.parameters) + ')'
        stability_checks = []
        if pair[0].requires:
            stability_checks.append('ensures ' + ' && '.join(pair[0].requires) + ';')
        stability_assumptions = []
        stability_assumptions.append('assume ' + invariant_text + ';')
        if pair[0].requires:
            stability_assumptions.append('assume ' + ' && '.join(pair[0].requires) + ';')
        
        generator = SpecificationGenerator()
        proc_constants = generator.get_constants(pair[0].parameters)
        proc_constants_declarations = generator.generate_const_text(proc_constants)
        specification_text = spec.preface + '\n' + proc_constants_declarations + '\n' + generator.generate_spec('stability', stability_checks, stability_assumptions, pair[1])
        try:
            message = Executor.execute_boogie(pair, specification_text, 'stability_' + pair[0].name + '_under_' + pair[1].name)
        except Exception as e:
            raise SafetyError(e)

        stability_checks = []
        if pair[1].requires:
            stability_checks.append('ensures ' + ' && '.join(pair[1].requires) + ';')
        stability_assumptions = []
        stability_assumptions.append('assume ' + invariant_text + ';')
        if pair[1].requires:
            stability_assumptions.append('assume ' + ' && '.join(pair[1].requires) + ';')
        
        generator = SpecificationGenerator()
        proc_constants = generator.get_constants(pair[1].parameters)
        proc_constants_declarations = generator.generate_const_text(proc_constants)
        specification_text = spec.preface + '\n' + proc_constants_declarations + '\n' + generator.generate_spec('stability', stability_checks, stability_assumptions, pair[0])
        try:
            message = Executor.execute_boogie(pair, specification_text, 'stability_' + pair[1].name + '_under_' + pair[0].name)
        except Exception as e:
            raise SafetyError(e)
        return True

    def check_stability_merge(self, spec):
        generator = SpecificationGenerator()
        merge_constants = generator.get_constants(spec.merge.parameters)
        merge_constants_declarations = generator.generate_const_text(merge_constants)
        
        invariant_text = spec.invariant.name + '(' + ','.join(param.name for param in spec.invariant.parameters) + ')'
        invariant_text = invariant_text + ' && ' + spec.invariant.name + '(' + ','.join('_' + param.name + '1' for param in spec.invariant.parameters) + ')'
        
        stability_checks = []
        for require in spec.merge.requires:
            requires = require
            for each in spec.merge.parameters:
                requires = generator.get_substituted_const(requires, each)
            stability_checks.append('ensures ' + requires + ';')
        stability_assumptions = []
        stability_assumptions.append('assume ' + invariant_text + ';')
        
        for each in spec.merge.requires:
            stability_assumptions.append('assume ' + each + ';')
        
        specification_text = spec.preface + '\n' + merge_constants_declarations + '\n' + generator.generate_spec('stability', stability_checks, stability_assumptions, spec.merge)
        try:
            message = Executor.execute_boogie([spec.merge], specification_text, 'stability_' + spec.merge.name)
        except Exception as e:
            raise SafetyError(e)
        return True

    # def generate_stability_check(self, spec, procedure, restrictions = None):
    #     if not restrictions:
    #         restrictions = []
    #     constants = []
    #     params0 = []
    #     params1 = []
    #     for param in procedure.parameters:
    #         constants.append('const _' + param.name + '0:' + param.datatype + ';')
    #         params0.append('_' + param.name + '0')
    #     for param in spec.merge.parameters:
    #         constants.append('const _' + param.name + '1:' + param.datatype + ';')
    #         params1.append('_' + param.name + '1')

    #     proc1 = pair[0].get_signature() + '\n{\n' + pair[0].implementation + '\n}\n'
    #     proc2 = pair[1].get_signature() + '\n{\n' + pair[1].implementation + '\n}\n'
        
    #     requires1 = pair[0].requires[:]
    #     requires2 = pair[1].requires[:]

    #     for each in pair[0].parameters:
    #         p = re.compile(r'\b' + each.name + r'\b')
    #         for i in range(len(requires1)):
    #             requires1[i] = p.sub('_' + each.name + '0', requires1[i])
    #     for each in pair[1].parameters:
    #         p = re.compile(r'\b' + each.name + r'\b')
    #         for i in range(len(requires2)):
    #             requires2[i] = p.sub('_' + each.name + '1', requires2[i])
            
    #     invariant_text = spec.invariant.name + '(' + ','.join(param.name for param in spec.invariant.parameters) + ')'
    #     stability_test_proc = 'procedure stability_test() \n modifies ' + ','.join(pair[0].modifies) + '; \n modifies ' + ','.join(pair[1].modifies) + '; \n'
    #     stability_test_proc = stability_test_proc + '{ \n assume ' + invariant_text + '; \n'
    #     if requires1:
    #         stability_test_proc = stability_test_proc + ' assume (' + ' && '.join(requires1) + '); \n '
    #     if requires2:
    #         stability_test_proc = stability_test_proc + ' assume (' + ' && '.join(requires2) + ');\n '
    #     if restrictions:
    #         stability_test_proc = stability_test_proc + ' assume (' + ' && '.join(restrictions) + ');\n '
    #     stability_test_proc = stability_test_proc + 'call ' + pair[0].name + '(' + ','.join(params0) + ');\n'
    #     stability_test_proc = stability_test_proc + 'call ' + pair[1].name + '(' + ','.join(params1) + ');\n}'
    #     if pair[0] == pair[1]:
    #         specification_text = spec.preface + '\n' + proc1 + '\n'.join(constants) + '\n' + stability_test_proc
    #     else:
    #         specification_text = spec.preface + '\n' + proc1 + proc2 + '\n'.join(constants) + '\n' + stability_test_proc
    #     return specification_text