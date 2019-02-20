from soteria.verifier import Verifier
import sys

if __name__ == "__main__":
    v = Verifier()
    Verifier.set_up_logger()
    v.analyze(sys.argv[1])