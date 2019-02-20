from soteria.debug_support.boogie_output_parser import BoogieOutputParser

class TestBoogieOutputParser:
    sample1 = '''input(168,1): Error BP5002: A precondition for this call might not hold.
input(146,1): Related location: This is the precondition that might not hold.
Execution trace:
    input(164,2): anon0
input(168,1): Error BP5002: A precondition for this call might not hold.
input(145,1): Related location: This is the precondition that might not hold.
Execution trace:
    input(164,2): anon0

Boogie program verifier finished with 2 verified, 2 errors'''

    sample2 = '''Boogie program verifier version 2.3.0.61016, Copyright (c) 2003-2014, Microsoft.
test_models/stability_decrement_transfer.bpl(167,1): Error BP5002: A precondition for this call might not hold.
test_models/stability_decrement_transfer.bpl(145,1): Related location: This is the precondition that might not hold.
Execution trace:
    test_models/stability_decrement_transfer.bpl(163,2): anon0

Boogie program verifier finished with 2 verified, 1 error'''

    def test_parse(self):
        parser = BoogieOutputParser()
        errors = parser.parse(self.sample1)
        assert len(errors) == 2
        assert errors[0].line == 168
        assert errors[0].code == 'BP5002'
        assert errors[0].message == 'A precondition for this call might not hold.'
        assert len(errors[0].related_locations) == 1
        assert errors[0].related_locations[0].line == 146
        assert errors[1].related_locations[0].line == 145