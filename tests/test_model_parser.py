from soteria.debug_support.model_parser import ModelParser

class TestModelParser:
    input1 = '''*** MODEL
    %lbl%@176 -> false
    %lbl%+83 -> true
    %lbl%+95 -> true
    counter@@0 -> 719
    counter@0 -> 1
    other -> 1
    tickleBool -> {
    true -> true
    false -> true
    else -> true
    }
    *** END_MODEL
    *** MODEL
    %lbl%@176 -> true
    %lbl%@180 -> false
    %lbl%+83 -> true
    %lbl%+95 -> true
    counter@@0 -> 0
    counter@0 -> 0
    other -> 1
    tickleBool -> {
    true -> true
    false -> true
    else -> true
    }
    *** END_MODEL
    '''

    input2 = '''*** MODEL
    %lbl%@131 -> false
    %lbl%+77 -> true
    %lbl%+95 -> true
    set -> |T@[Int]Bool!val!0|
    set@0 -> |T@[Int]Bool!val!1|
    value -> 0
    gteq -> {
    |T@[Int]Bool!val!1| |T@[Int]Bool!val!0| -> false
    else -> false
    }
    tickleBool -> {
    true -> true
    false -> true
    else -> true
    }
    Store_[$int]$bool -> {
    |T@[Int]Bool!val!0| 0 false -> |T@[Int]Bool!val!1|
    else -> |T@[Int]Bool!val!1|
    }
    i!0!0 -> {
    |T@[Int]Bool!val!0| |T@[Int]Bool!val!1| -> 0
    else -> 0
    }
    Select_[$int]$bool -> {
    |T@[Int]Bool!val!0| 0 -> true
    |T@[Int]Bool!val!1| 0 -> false
    else -> true
    }
    *** END_MODEL
    '''

    def test_parse_number_of_models(self):
        parser = ModelParser()
        models = parser.parse(self.input1)
        assert len(models) == 2
        models = parser.parse(self.input2)
        assert len(models) == 1

    def test_parser_model_simple_dictionary(self):
        parser = ModelParser()
        models = parser.parse(self.input1)

        assert len(models[0]) == 3
        assert 'counter@@0' in models[0]
        assert models[0]['counter@@0'] == '719'
        assert 'counter@0' in models[0]
        assert models[0]['counter@0'] == '1'
        assert 'other' in models[0]
        assert models[0]['other'] == '1'

        assert len(models[1]) == 3
        assert 'counter@@0' in models[1]
        assert models[1]['counter@@0'] == '0'
        assert 'counter@0' in models[1]
        assert models[1]['counter@0'] == '0'
        assert 'other' in models[1]
        assert models[1]['other'] == '1'
 
    def test_parser_model_dictionary_with_function(self):
        parser = ModelParser()
        models = parser.parse(self.input2)

        assert len(models[0]) == 8
        assert 'set' in models[0]
        assert models[0]['set'] == '|T@[Int]Bool!val!0|'
        assert 'set@0' in models[0]
        assert models[0]['set@0'] == '|T@[Int]Bool!val!1|'
        assert 'value' in models[0]
        assert models[0]['value'] == '0'
        assert 'gteq -> |T@[Int]Bool!val!1| |T@[Int]Bool!val!0|' in models[0]
        assert models[0]['gteq -> |T@[Int]Bool!val!1| |T@[Int]Bool!val!0|'] == 'false'
        assert 'Store_[$int]$bool -> |T@[Int]Bool!val!0| 0 false' in models[0]
        assert models[0]['Store_[$int]$bool -> |T@[Int]Bool!val!0| 0 false'] == '|T@[Int]Bool!val!1|'
        assert 'i!0!0 -> |T@[Int]Bool!val!0| |T@[Int]Bool!val!1|' in models[0]
        assert models[0]['i!0!0 -> |T@[Int]Bool!val!0| |T@[Int]Bool!val!1|'] == '0'
        assert 'Select_[$int]$bool -> |T@[Int]Bool!val!0| 0' in models[0]
        assert models[0]['Select_[$int]$bool -> |T@[Int]Bool!val!0| 0'] == 'true'
        assert 'Select_[$int]$bool -> |T@[Int]Bool!val!1| 0' in models[0]
        assert models[0]['Select_[$int]$bool -> |T@[Int]Bool!val!1| 0'] == 'false'
        