class ModelParser:
    def parse(self, input):
        models = []
        model = {}
        tickleBoolStarted = False
        functionStarted = False
        functionName = ''
        stateStarted = False
        for line in input.split('\n'):
            if line.strip():
                if line.strip() == '*** MODEL':
                    model = {}
                elif line.strip().startswith('*** STATE'):
                    #this is a temporary thing, if you need state information, extract from here
                    stateStarted = True
                elif line.strip().startswith('*** END_STATE'):
                    #this is a temporary thing, if you need state information, extract from here
                    stateStarted = False
                elif stateStarted:
                    continue
                elif line.strip().startswith('%lbl%'):
                    continue
                elif line.strip().startswith('else'):
                    continue
                elif line.strip().startswith('tickleBool'):
                    tickleBoolStarted = True
                    continue
                elif tickleBoolStarted:
                    if line.strip().startswith('}'):
                        tickleBoolStarted = False
                elif line.strip() == '*** END_MODEL':
                    models.append(model)
                elif line.strip().endswith('{'):
                    functionStarted = True
                    functionName = line[:line.index('->')].strip()
                elif line.strip().startswith('}') and functionStarted:
                    functionStarted = False
                elif functionStarted:
                    params = line[:line.index('->')].strip()
                    key = functionName + ' -> ' + params
                    value = line[line.index('->') + 2:].strip()
                    model[key] = value
                else:
                    key = line[:line.index('->')].strip()
                    value = line[line.index('->') + 2:].strip()
                    model[key] = value
        return models
