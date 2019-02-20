from datetime import datetime
from shutil import copy2, copytree
import os
import errno
import subprocess
import re
from soteria.exceptions import BoogieParseError, BoogieTypeError, BoogieVerificationError, BoogieUnknownError
from soteria.debug_support.debugger import Debugger

##TODO : refactor this class

class Executor:

    #@classmethod
    def execute_boogie(operations, specification, name = 'specification'):
        model_file_path = 'results/' + name + '.model'
        spec_file = Executor.create_spec_file(specification, name)
        path_to_boogie = '/boogie/Binaries/Boogie.exe'
        proc = subprocess.Popen(['mono', path_to_boogie, '-mv:' + model_file_path, spec_file], stdout=subprocess.PIPE)
        out = proc.communicate()[0]
        status = Executor.get_execution_status(name, out.decode("utf-8"), operations, spec_file, model_file_path)
        return status

    def create_spec_file(text, name):
        with open('results/' + name + '.bpl', 'w') as f:
            f.write(text)
        return 'results/' + name + '.bpl'

    def get_execution_status(name, result, operations, spec_file, model_file_path):
        if 'parse errors detected' in result:
            raise BoogieParseError(result + '\n')
        if 'type checking errors detected' in result:
            raise BoogieTypeError(result + '\n')
        if 'Boogie program verifier finished with' in result:
            errors = Executor.get_number_of_errors(result[result.index('Boogie program verifier finished with') + 38:])
            if errors > 0:
                specification = open(spec_file).readlines()
                debugger = Debugger()
                info = debugger.get_debug_info(operations, specification, result, model_file_path)
                raise BoogieVerificationError(name + '::::::\n' + info + '\n')
            if errors == 0:
                return result
        raise BoogieUnknownError(result)

    def get_number_of_errors(text):
        p = re.compile('\d error')
        m = p.search(text) 
        if m:
            e = re.compile('\d')
            n = e.search(m.group(0))
            return int(n.group(0))
        return -1
