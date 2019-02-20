#from soteria.exceptions import EmptyInputError, TerminalError
from soteria.checks.syntax_checker import SyntaxChecker
from soteria.parser import Parser
from soteria.checks.compliance_checker import ComplianceChecker
from soteria.checks.convergence_checker import ConvergenceChecker
from soteria.checks.safety_checker import SafetyChecker
import os
import coloredlogs, logging
from soteria.token_generation.token_generator import TokenGenerator

class Verifier:
    def set_up_logger():
        coloredlogs.install()
        # set up logging to file 
        logging.basicConfig(level=logging.DEBUG,
                            format='%(asctime)s %(levelname)-8s: %(message)s',
                            datefmt='%y-%m-%d %H:%M',
                            filename='results/myapp.log',
                            filemode='a')
        # define a Handler which writes INFO messages or higher to the sys.stderr
        console = logging.StreamHandler()
        console.setLevel(logging.INFO)
        # set a format which is simpler for console use
        # formatter = logging.Formatter('%(levelname)-8s: %(message)s')
        # tell the handler to use this format
        # console.setFormatter(formatter)
        # add the handler to the root logger
        # logging.getLogger('').addHandler(console)

    def analyze(self, specification_path):
        if not specification_path:
            logging.error('Please provide a specification file!')
            return False
        if specification_path[specification_path.rindex('.'):].strip().lower() != '.spec':
            logging.error('Specification file needs to have .spec extension.')
            return False
        try:
            spec_file = open(specification_path)
            spec_name = self.get_specification_name(specification_path)
            logging.info('************ ' + spec_name + ' ***************')
            logging.info('Checking the syntax')
            spec_content = spec_file.readlines()
            stx_chkr = SyntaxChecker()
            message = stx_chkr.check(spec_name, spec_content)
            logging.info('Parsing the specification')
            parser = Parser()
            specification = parser.parse(spec_name, spec_content)
            logging.info('Checking the well-formedness of the specification')
            compliance_checker = ComplianceChecker()
            compliance_checker.check(specification)
            logging.info('Checking convergence')
            convergence_checker = ConvergenceChecker()
            convergence_checker.check(specification)
            logging.info('Checking safety')
            safety_checker = SafetyChecker()
            safe, failed = safety_checker.check(specification)
            if safe:
                logging.info('The specification is safe!!!')
            else:
                #generate tokens here
                raise Exception
            # else:
            #     logging.info('starting token generation')
            #     for failure in failed:
            #         #failure is a pair of procedure names which failed stability check
            #         token_generator = TokenGenerator()
            #         tokens = token_generator.generate_tokens(specification, failed) 
            #         logging.info('The tokens are as follows ::\n' + token_generator.convert_to_text(tokens))
            #         if tokens:
            #             logging.info('The possible token(s) for ensuring stability of ' + failure[0].name + ' and ' +failure[1].name +' ::\n' + str(tokens)+ '\n')
            #         else:
            #             logging.info('Not able to determine a token for the stability of ' + failure[0].name + ' and ' +failure[1].name)
                
        except Exception as e:
            logging.error(str(e) + '\n')
            return False
        return True

    def get_specification_name(self, path):
        folder, file_name = os.path.split(path)
        spec_name = file_name[:file_name.index('.')]
        return spec_name