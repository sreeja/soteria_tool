# from soteria.token_generation.token_generator import TokenGenerator
# from soteria.components.specification import Specification
# from soteria.components.variable import Variable
# from soteria.components.parameter import Parameter
# from soteria.components.procedure import Procedure
# from soteria.components.function import Function
# from soteria.exceptions import NoTokenFoundError
# from soteria.token_generation.token_generator import Token
# import pytest

# class TestTokenGenerator:

#     def get_create_order_proc(self):
#         create_order = Procedure('createOrder', 40)
#         create_order.add_parameter(Parameter('id', 'OrderId'))
#         create_order.add_parameter(Parameter('usr', 'UserId'))
#         create_order.add_modifies('UserOrders')
#         create_order.add_ensures('forall o:OrderId :: (o == id ==> (UserOrders[o][created] == true && UserOrders[o][user] == usr && UserOrders[o][placed] == false && UserOrders[o][cancelled] == false && UserOrders[o][processed] == false && (forall b:ISBN :: UserOrders[o][items][b] == 0))) && (o != id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b])))')
#         create_order.add_requires('UserOrders[id][created] == false && UserOrders[id][user] == usr')
#         create_order.set_implementation('assume false;')
#         return create_order

#     def get_cancel_order_proc(self):
#         cancel_order = Procedure('cancelOrder', 50)
#         cancel_order.add_parameter(Parameter('id', 'OrderId'))
#         cancel_order.add_parameter(Parameter('usr', 'UserId'))
#         cancel_order.add_modifies('UserOrders')
#         cancel_order.add_ensures('(forall o:OrderId :: (o == id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == true && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))) && (o != id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))))')
#         cancel_order.add_requires('UserOrders[id][placed] == true && UserOrders[id][processed] == false && UserOrders[id][user] == usr')
#         cancel_order.set_implementation('assume false;')
#         return cancel_order

#     def get_process_order_proc(self):
#         process_order = Procedure('processOrder', 60)
#         process_order.add_parameter(Parameter('id', 'OrderId'))
#         process_order.add_modifies('UserOrders')
#         process_order.add_modifies('BookStore')
#         process_order.add_ensures('(forall o:OrderId :: (o == id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == true && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))) && (o != id ==> (UserOrders[o][created] == old(UserOrders)[o][created] && UserOrders[o][user] == old(UserOrders)[o][user] && UserOrders[o][placed] == old(UserOrders)[o][placed] && UserOrders[o][cancelled] == old(UserOrders)[o][cancelled] && UserOrders[o][processed] == old(UserOrders)[o][processed] && (forall b:ISBN :: UserOrders[o][items][b] == old(UserOrders)[o][items][b]))))')
#         process_order.add_requires('UserOrders[id][placed] == true && UserOrders[id][processed] == false && UserOrders[id][cancelled] == false')
#         process_order.set_implementation('assume false;')
#         return process_order

#     def get_merge_order(self):
#         merge_order = Procedure('mergeOrders', 70)
#         merge_order.add_parameter(Parameter('incoming', 'Order'))
#         merge_order.add_modifies('UserOrders')
#         merge_order.add_ensures('forall o:OrderId :: (UserOrders[o][created] == (old(UserOrders)[o][created] || incoming[o][created])) &&  (UserOrders[o][placed] == (old(UserOrders)[o][placed] || incoming[o][placed])) &&  (UserOrders[o][cancelled] == (old(UserOrders)[o][cancelled] || incoming[o][cancelled])) && (UserOrders[o][processed] == (old(UserOrders)[o][processed] || incoming[o][processed])) && (forall b:ISBN :: (UserOrders[o][items][b] == max(old(UserOrders)[o][items][b], incoming[o][items][b])))')
#         merge_order.set_implementation('assume false;')
#         return merge_order

#     def get_merge_store(self):
#         merge_store = Procedure('mergeStore', 70)
#         merge_store.add_parameter(Parameter('incoming', 'Store'))
#         merge_store.add_modifies('BookStore')
#         merge_store.add_ensures('(forall b:ISBN, r:ReplicaID :: BookStore[b][P][r] == max(old(BookStore)[b][P][r], incoming[b][P][r]) && BookStore[b][N][r] == max(old(BookStore)[b][N][r], incoming[b][N][r]))')
#         merge_store.set_implementation('assume false;')
#         return merge_store

#     def get_spec(self):
#         specification = Specification('sample')
#         specification.add_variable(Variable('BookStore', 'Store', 23))
#         specification.add_variable(Variable('UserOrders', 'Order', 24))
#         specification.set_preface('''type ISBN;
# type Store = [ISBN]Counter;
# type Selector;
# type Counter = [Selector]int;
# const unique P:Selector;
# const unique N:Selector;
# axiom(forall s:Selector :: s == P || s == N);
# function value(c:Counter) returns(int){  (c[P]-c[N]) }	
# function inc(c:Counter, oldC:Counter, value:int) returns (bool){  (c[P] == oldC[P] + value) && (c[N] == oldC[N]) }
# function dec(c:Counter, oldC:Counter, value:int) returns (bool){  (c[P] == oldC[P]) && (c[N] == oldC[N] + value) }
# function max(a:int, b:int) returns(int){  (if a > b then a else b)}
# type UserId;
# type OrderId;
# type Field a;
# type Order = [OrderId]<a>[Field a]a;
# const unique user: Field UserId;
# const unique items: Field [ISBN]int;
# const unique created:Field bool;
# const unique placed:Field bool;
# const unique cancelled:Field bool;
# const unique processed: Field bool;
# axiom(forall orders:Order, o:OrderId :: orders[o][created] == false ==> (orders[o][placed] == false && orders[o][cancelled] == false && orders[o][processed] == false && (forall b:ISBN :: orders[o][items][b] == 0)));
# var BookStore:Store;
# var UserOrders:Order;
# function gteq_store(S1:Store, S2:Store) returns(bool){  (forall b:ISBN :: value(S1[b]) >= value(S2[b]))}
# function gteq_order(O1:Order, O2:Order) returns(bool){  (forall o:OrderId :: (O2[o][created] ==> O1[o][created]) && (O2[o][placed] ==> O1[o][placed]) && (O2[o][cancelled] ==> O1[o][cancelled]) && (O2[o][processed] ==> O1[o][processed]) && (forall b:ISBN :: O1[o][items][b] >= O2[o][items][b]))}
# function inv(BookStore:Store, UserOrders:Order) returns(bool){  (forall b:ISBN :: value(BookStore[b]) >= 0)}
# ''')
#         invariant = Function('inv', 35)
#         invariant.add_param(Parameter('BookStore', 'Store'))
#         invariant.add_param(Parameter('UserOrders', 'Order'))
#         invariant.set_return('bool')
#         specification.add_invariant(invariant)
        
#         specification.add_procedure(self.get_create_order_proc())
#         specification.add_procedure(self.get_cancel_order_proc())
#         specification.add_procedure(self.get_process_order_proc())

#         specification.add_merge(self.get_merge_order())
#         specification.add_merge(self.get_merge_store())
#         return specification

#     def test_get_token_suggestions_one_token(self):
#         #uses cancelOrder-processOrder
#         specification = self.get_spec()

#         generator = TokenGenerator()
#         tokens = generator.get_token_suggestions(specification, (self.get_cancel_order_proc(), self.get_process_order_proc()))
#         assert len(tokens) == 1
#         assert tokens[0] in ['_id0 != _id1', '_id1 != _id0']

#     def test_get_token_suggestions_multiple_tokens(self):
#         specification = self.get_spec()
#         generator = TokenGenerator()
#         tokens = generator.get_token_suggestions(specification, (self.get_create_order_proc(), self.get_create_order_proc()))
#         assert len(tokens) == 3
#         expected = ['_id0 != _id1', '_id1 != _id0', '_usr0 != _usr1', '_usr1 != _usr0', '_id0 != _id1 && _usr0 != _usr1', '_id1 != _id0 && _usr0 != _usr1', '_id1 != _id0 && _usr1 != _usr0', '_id0 != _id1 && _usr1 != _usr0']
#         assert tokens[0] in expected
#         assert tokens[1] in expected

#     def test_get_token_suggestions_no_token(self):
#         specification = self.get_spec()
#         generator = TokenGenerator()
#         tokens = generator.get_token_suggestions(specification, (self.get_merge_order(), self.get_create_order_proc()))
#         assert len(tokens) == 0

#     def test_generate_tokens(self):
#         specification = self.get_spec()
#         generator = TokenGenerator()
#         tokens = generator.generate_tokens(specification, [(self.get_create_order_proc(), self.get_create_order_proc()), (self.get_merge_order(), self.get_create_order_proc()), (self.get_cancel_order_proc(), self.get_process_order_proc()), (self.get_process_order_proc(), self.get_cancel_order_proc()), (self.get_merge_order(), self.get_process_order_proc()), (self.get_merge_order(), self.get_cancel_order_proc()), (self.get_merge_store(), self.get_process_order_proc()), (self.get_process_order_proc(), self.get_process_order_proc())])
#         assert len(tokens) == 3
#         assert len(tokens['createOrder'].merges) == 1
#         assert len(tokens['createOrder'].operations_shared) == 1
#         assert len(tokens['cancelOrder'].merges) == 1
#         assert len(tokens['cancelOrder'].operations_shared) == 1
#         assert len(tokens['processOrder'].merges) == 2
#         assert len(tokens['processOrder'].operations_shared) == 2

#     def test_convert_to_text(self):
#         tokens = {}
#         tokens['createOrder'] = Token('createOrder')
#         tokens['createOrder'].add_merge('mergeOrder')
#         tokens['createOrder'].add_operation('createOrder', ['_id0 != _id1', '_usr0 != _usr1', '_id0 != _id1 && _usr0 != _usr1'])
#         tokens['processOrder'] = Token('processOrder')
#         tokens['processOrder'].add_merge('mergeOrder')
#         tokens['processOrder'].add_merge('mergeStore')
#         tokens['processOrder'].add_operation('processOrder',  ['_storeloc0 != _storeloc1 && _id0 != _id1'])
#         tokens['processOrder'].add_operation('cancelOrder',  ['_id0 != _id1'])
#         generator = TokenGenerator()
#         text = generator.convert_to_text(tokens)
#         assert "createOrder:" in text
#         assert "mergeOrder should be executed while acquiring the token." in text
#         assert "Token shared with createOrder on ['_id0 != _id1', '_usr0 != _usr1', '_id0 != _id1 && _usr0 != _usr1']" in text
#         assert "processOrder:" in text
#         assert "mergeOrder and mergeStore should be executed while acquiring the token." in text
#         assert "Token shared with processOrder on ['_storeloc0 != _storeloc1 && _id0 != _id1'] and cancelOrder on ['_id0 != _id1']" in text
        

        
        
