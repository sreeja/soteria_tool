# Soteria
Verifies the specification of distributed applications which use state-based CRDTs and work on a causally consistent datastore.

# Requirements
[Docker Compose](https://docs.docker.com/compose/install/)

# Usage
`docker-compose run soteria specs/<application_name>.spec`

Note : The specification directory must be inside the folder soteria.

# Writing specifications
The specifications are written in Boogie with annotations. 
To get yourself failiarised with Boogie, there is a playground offered at https://rise4fun.com/Boogie/.
`specification_template.txt` gives an overview on the template of the specification.

# Checks performed by the tool
The tool performs the following checks

## Syntax check
Ensures whether the specificaiton respects Boogie's syntax and there are no anomalies in the specification.
- ![#1589F0](https://placehold.it/15/1589F0/000000?text=+) The annotations from the code is removed and fed into Boogie solver which does the checks for us.

## Compliance check
Ensures whether the specification meets the specification template

### Invariant check
Checks the following
- the number of function parameters = number of global variables
- all global variables should have a function parameter with the same name
- return value should be bool

### Greater than or equal to function check
Checks the following
- all global variables should be present in greater than function as pairs with suffixes `1` and `2`
- must have return value bool

### Merge procedure check
Checks the following
- number of parameters of merge = number of variables in modifies clause = number of variables declared
- all modifies variable must have a parameter with the same datatype
- the name of the parameter corresponding to each global variable should be with suffix `1`

## Convergence check
Ensures whether the state is a semi-lattice. It checks whether each update is monotonically non-decreasing and the merge is the least upper bound.

## Safety check
This checks whether each update and merge satisfies the invariant and the pre-condition of merge.

# Development

## Running tests
`docker-compose run test-unit`