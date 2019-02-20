from soteria.parser import Parser

class TestParser:

    def get_spec_string(self):
        return open('tests/test_specs/parser_test.spec').readlines()

    def get_spec(self):
        sample = self.get_spec_string()
        parser = Parser()
        spec = parser.parse('sample', sample)
        return spec
    
    def test_parse_name_set(self):
        spec = self.get_spec()
        assert spec.name == 'sample'

    def test_parse_preface_set(self):
        spec = self.get_spec()
        assert spec.preface != ''

    def test_extract_preface_annotations_commented(self):
        sample = []
        sample.append('var counter:int; \n')
        sample.append('@invariant\n')
        sample.append('function abdsflsjdfsd(a:int) returns(bool); \n')
        sample.append('procedure abdsfls(jdf:sd) \n')
        sample.append('{ \n')
        sample.append('//test comment \n')
        sample.append('}\n //test\n')
        sample.append('var a:int;')
        parser = Parser()
        spec = parser.parse('sample', sample)
        assert spec.preface == 'var counter:int; \n//@invariant\nfunction abdsflsjdfsd(a:int) returns(bool); \n//procedure abdsfls(jdf:sd) \n//{ \n////test comment \n//}\n //test\nvar a:int;'
        
    def test_parse_variables_set(self):
        spec = self.get_spec()
        assert len(spec.variables) == 2
        assert spec.variables[0].name == 'R'
        assert spec.variables[1].name == 'U'
        assert spec.variables[0].datatype == 'matrix2d'
        assert spec.variables[1].datatype == 'matrix1d'

    # def test_parse_invariants_set(self):
    #     spec = self.get_spec()
    #     assert len(spec.invariants) == 2

    def test_parse_invariant_inv(self):
        spec = self.get_spec()
        assert spec.invariant.name == 'inv'
        assert spec.invariant.position  == 15
        assert len(spec.invariant.parameters) == 2
        assert spec.invariant.parameters[0].name == 'R'
        assert spec.invariant.parameters[1].name == 'U'
        assert spec.invariant.parameters[0].datatype == 'matrix2d'
        assert spec.invariant.parameters[1].datatype == 'matrix1d'
    
    # def test_parse_invariant_invmock(self):
    #     spec = self.get_spec()
    #     assert spec.invariants[1].name == 'invmock'
    #     assert spec.invariants[1].position == 69
    #     assert len(spec.invariants[1].parameters) == 2
    #     assert spec.invariants[1].parameters[0].name in ['R', 'U']
    #     assert spec.invariants[1].parameters[1].name in ['R', 'U']
    #     assert spec.invariants[1].parameters[0].datatype in ['matrix2d', 'matrix1d']
    #     assert spec.invariants[1].parameters[1].datatype in ['matrix2d', 'matrix1d']

    # def test_parse_gteqs_set(self):
    #     spec = self.get_spec()
    #     assert len(spec.gteqs) == 2

    def test_parse_gteq(self):
        spec = self.get_spec()
        assert spec.gteq.name == 'gteq'
        assert spec.gteq.position == 21
        assert len(spec.gteq.parameters) == 4
        assert spec.gteq.parameters[0].name == 'R1'
        assert spec.gteq.parameters[1].name == 'R2'
        assert spec.gteq.parameters[2].name == 'U1'
        assert spec.gteq.parameters[3].name == 'U2'
        assert spec.gteq.parameters[0].datatype  == 'matrix2d'
        assert spec.gteq.parameters[1].datatype  == 'matrix2d'
        assert spec.gteq.parameters[2].datatype  == 'matrix1d'
        assert spec.gteq.parameters[3].datatype  == 'matrix1d'

    # def test_parse_gteqs_U(self):
    #     spec = self.get_spec()
    #     assert spec.gteqs[1].name == 'gteq_1d'
    #     assert spec.gteqs[1].position == 80
    #     assert len(spec.gteqs[1].parameters) == 2
    #     assert spec.gteqs[1].parameters[0].name in ['U1', 'U2']
    #     assert spec.gteqs[1].parameters[1].name in ['U1', 'U2']
    #     assert spec.gteqs[1].parameters[0].datatype == 'matrix1d'
    #     assert spec.gteqs[1].parameters[1].datatype == 'matrix1d'      

    # def test_parse_merges_set(self):
    #     spec = self.get_spec()
    #     assert len(spec.merges) == 2

    def test_parse_merge(self):
        spec = self.get_spec()
        assert spec.merge.name  == 'merge'
        assert spec.merge.position == 26
        assert len(spec.merge.parameters) == 2
        assert len(spec.merge.modifies) == 2
        assert len(spec.merge.ensures) == 1
        assert len(spec.merge.requires) == 0
        assert spec.merge.parameters[0].name  == 'newR'
        assert spec.merge.parameters[0].datatype == 'matrix2d'
        assert spec.merge.parameters[1].name  == 'newU'
        assert spec.merge.parameters[1].datatype == 'matrix1d'
        assert spec.merge.modifies[0] == 'R'
        assert spec.merge.ensures[0] == 'update2dmatrix(newR, old(R), R) && update1dmatrix(newU, old(U), U)'
        # import ipdb
        # ipdb.set_trace()
        assert spec.merge.implementation == 'assume false;'        

    # def test_parse_merge_U(self):
    #     spec = self.get_spec()
    #     assert spec.merges[1].name == 'mergeU'
    #     assert spec.merges[1].position == 117
    #     assert len(spec.merges[1].parameters) == 1
    #     assert len(spec.merges[1].modifies) == 1
    #     assert len(spec.merges[1].ensures) == 1
    #     assert len(spec.merges[1].requires) == 0
    #     assert spec.merges[1].parameters[0].name == 'newU'
    #     assert spec.merges[1].parameters[0].datatype == 'matrix1d'
    #     assert spec.merges[1].modifies[0] == 'U'
    #     assert spec.merges[1].ensures[0] == 'update1dmatrix(newU, old(U), U)'
    #     assert spec.merges[1].implementation == 'assume false;'

    def test_parse_procedures_set(self):
        spec = self.get_spec()
        assert len(spec.procedures) == 3

    def test_parse_procedures_inc(self):
        spec = self.get_spec()
        assert spec.procedures[0].name == 'increment'
        assert spec.procedures[0].position == 33
        assert len(spec.procedures[0].parameters) == 2
        assert len(spec.procedures[0].modifies) == 1
        assert len(spec.procedures[0].ensures) == 0
        assert len(spec.procedures[0].requires) == 2
        assert spec.procedures[0].parameters[0].name in ['id', 'n']
        assert spec.procedures[0].parameters[1].name in ['id', 'n']
        assert spec.procedures[0].parameters[0].datatype == 'int'
        assert spec.procedures[0].parameters[1].datatype == 'int'
        assert spec.procedures[0].modifies[0] == 'R'
        assert spec.procedures[0].requires[0] == 'n > 0', 'id >= 0 && id < replicas'
        assert spec.procedures[0].requires[1] == 'id >= 0 && id < replicas'
        assert spec.procedures[0].implementation == 'R[id][id] := R[id][id] + n;'
        assert spec.procedures[0].get_signature() == 'procedure increment(id:int, n:int)\nmodifies R;\nrequires (n > 0);\nrequires (id >= 0 && id < replicas);\n'
        
    def test_parse_procedures_dec(self):
        spec = self.get_spec()
        assert spec.procedures[1].name == 'decrement'
        assert spec.procedures[1].position == 40
        assert len(spec.procedures[1].parameters) == 2
        assert len(spec.procedures[1].modifies) == 1
        assert len(spec.procedures[1].ensures) == 0
        assert len(spec.procedures[1].requires) == 3
        assert spec.procedures[1].parameters[0].name in ['id', 'n']
        assert spec.procedures[1].parameters[1].name in ['id', 'n']
        assert spec.procedures[1].parameters[0].datatype == 'int'
        assert spec.procedures[1].parameters[1].datatype == 'int'
        assert spec.procedures[1].modifies[0] == 'U'
        assert spec.procedures[1].requires[0] == 'n > 0'
        assert spec.procedures[1].requires[1] == 'id >= 0 && id < replicas'
        assert spec.procedures[1].requires[2] == 'local_rights(id, R, U) >= n'
        assert spec.procedures[1].implementation == 'U[id] := U[id] + n;'


    def test_parse_procedures_transfer(self):
        spec = self.get_spec()
        assert spec.procedures[2].name == 'transfer'
        assert spec.procedures[2].position == 48
        assert len(spec.procedures[2].parameters) == 3
        assert len(spec.procedures[2].modifies) == 1
        assert len(spec.procedures[2].ensures) == 0
        assert len(spec.procedures[2].requires) == 3
        assert spec.procedures[2].parameters[0].name in ['n', 'from', 'to']
        assert spec.procedures[2].parameters[1].name in ['n', 'from', 'to']
        assert spec.procedures[2].parameters[2].name in ['n', 'from', 'to']
        assert spec.procedures[2].parameters[0].datatype == 'int'
        assert spec.procedures[2].parameters[1].datatype == 'int'
        assert spec.procedures[2].parameters[2].datatype == 'int'
        assert spec.procedures[2].modifies[0] == 'R'
        assert spec.procedures[2].requires[0] == 'n > 0'
        assert spec.procedures[2].requires[1] == 'from >= 0 && from < replicas  && to >= 0 && to < replicas && from != to'
        assert spec.procedures[2].requires[2] == 'local_rights(from, R, U) >= n'
        assert spec.procedures[2].implementation == 'R[from][to] := R[from][to] + n;'      
