from soteria.executor import Executor
from soteria.exceptions import EmptyInputError, BoogieSyntaxError

class SyntaxChecker:
    def check(self, name, spec):
        if not name:
            raise EmptyInputError('Name of the specification is not defined')
        cleaned_spec = self._comment_annotations(spec)
        try:
            message = Executor.execute_boogie(None, ''.join(cleaned_spec), name)
        except Exception as e:
            raise BoogieSyntaxError(e)
        return message

    def _comment_annotations(self, spec):
        cleaned = []
        for line in spec:
            if line.startswith('@'):
                cleaned.append('//' + line)
            else:
                cleaned.append(line)
        return cleaned
