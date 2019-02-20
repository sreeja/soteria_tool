import sys

class EmptyInputError(Exception):
    pass

class ComplianceError(Exception):
    pass

# class NonTerminalError(Exception):
#     pass

# class TerminalError(Exception):
#     pass

# class ParseError(Exception):
#     pass
    
class BoogieParseError(Exception):
    pass

class BoogieSyntaxError(Exception):
    pass

class BoogieTypeError(Exception):
    pass

class BoogieUnknownError(Exception):
    pass

class BoogieVerificationError(Exception):
    pass

class ConvergenceError(Exception):
    pass

class SafetyError(Exception):
    pass

class NoTokenFoundError(Exception):
    pass
