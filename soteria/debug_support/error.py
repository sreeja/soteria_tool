class Error:
    def __init__(self, line, error_code, error_message):
        self.line = line
        self.code = error_code
        self.message = error_message
        self.related_locations = []
        self.expression = ''

    def add_related_location(self, rel_loc):
        self.related_locations.append(rel_loc)

    def set_expression(self, expr):
        self.expression = expr

class RelatedLocation:
    def __init__(self, line, message):
        self.line = line
        self.message = message
        self.expression = ''

    def set_expression(self, expr):
        self.expression = expr
