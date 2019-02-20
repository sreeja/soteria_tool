from soteria.debug_support.error import Error, RelatedLocation

class BoogieOutputParser:
    def parse(self, text):
        errors = []
        current_error = None
        for line in text.split('\n'):
            if '): Error ' in line:
                error_line = int(line[line.index('(')+1 :line.index(',')].strip())
                error_code = line[line.index(': Error ') + 8:line.rindex(':')].strip()
                error_message = line[line.rindex(':') + 1:].strip()
                current_error = Error(error_line, error_code, error_message)
                errors.append(current_error)
            if '): Related location:' in line:
                loc_line = int(line[line.index('(')+1 :line.index(',')].strip())
                loc_message = line[line.rindex(':') + 1:].strip()
                related_loc = RelatedLocation(loc_line, loc_message)
                current_error.add_related_location(related_loc)
        return errors
