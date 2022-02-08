(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_A_19_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_A_19_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int))
(=> (= error_0 0) (nondet_interface_1_A_19_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_0 x_2_0))))


(declare-fun |summary_3_constructor_10_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_4_function_f__18_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |summary_5_function_f__18_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_13_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (nondet_interface_1_A_19_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_1 x_2_1) true) (and (= error_0 0) (summary_5_function_f__18_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2 _13_1))) (nondet_interface_1_A_19_0 error_1 this_0 abi_0 crypto_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |interface_6_B_26_0| (Int |abi_type| |crypto_type| |state_type| Int Int ) Bool)
(declare-fun |nondet_interface_7_B_26_0| (Int Int |abi_type| |crypto_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_constructor_8_B_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (_13_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int))
(=> (= error_1 0) (nondet_interface_7_B_26_0 error_1 this_0 abi_0 crypto_0 state_0 y_25_0 x_2_0 state_0 y_25_0 x_2_0))))


(declare-fun |summary_9_constructor_10_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_10_function_f__18_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(declare-fun |summary_11_function_f__18_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_13_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (nondet_interface_7_B_26_0 error_1 this_0 abi_0 crypto_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1) true) (and (= error_1 0) (summary_11_function_f__18_26_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 y_25_1 x_2_1 state_2 y_25_2 x_2_2 _13_1))) (nondet_interface_7_B_26_0 error_2 this_0 abi_0 crypto_0 state_0 y_25_0 x_2_0 state_2 y_25_2 x_2_2))))


(declare-fun |interface_12_C_39_0| (Int |abi_type| |crypto_type| |state_type| Int Int ) Bool)
(declare-fun |nondet_interface_13_C_39_0| (Int Int |abi_type| |crypto_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_constructor_14_C_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (_13_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (= error_2 0) (nondet_interface_13_C_39_0 error_2 this_0 abi_0 crypto_0 state_0 y_25_0 x_2_0 state_0 y_25_0 x_2_0))))


(declare-fun |summary_15_constructor_10_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_16_function_f__18_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(declare-fun |summary_17_function_f__18_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_13_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (nondet_interface_13_C_39_0 error_2 this_0 abi_0 crypto_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1) true) (and (= error_2 0) (summary_17_function_f__18_39_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 y_25_1 x_2_1 state_2 y_25_2 x_2_2 _13_1))) (nondet_interface_13_C_39_0 error_3 this_0 abi_0 crypto_0 state_0 y_25_0 x_2_0 state_2 y_25_2 x_2_2))))


(declare-fun |summary_18_function_g__38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_19_function_g__38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_13_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (nondet_interface_13_C_39_0 error_3 this_0 abi_0 crypto_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1) true) (and (= error_3 0) (summary_19_function_g__38_39_0 error_4 this_0 abi_0 crypto_0 tx_0 state_1 y_25_1 x_2_1 state_2 y_25_2 x_2_2))) (nondet_interface_13_C_39_0 error_4 this_0 abi_0 crypto_0 state_0 y_25_0 x_2_0 state_2 y_25_2 x_2_2))))


(declare-fun |block_20_function_f__18_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |block_21_f_17_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(block_20_function_f__18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _13_1)))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (block_20_function_f__18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _13_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_21_f_17_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _13_1))))


(declare-fun |block_22_return_function_f__18_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (block_21_f_17_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _13_1) (and (= _13_2 expr_15_0) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_2_1) (and (= _13_1 0) true))))) true) (block_22_return_function_f__18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _13_2))))


(declare-fun |block_23_return_ghost_f_16_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (block_23_return_ghost_f_16_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _13_2) (and (= _13_2 expr_15_0) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_2_1) (and (= _13_1 0) true))))) true) (block_22_return_function_f__18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _13_2))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (block_22_return_function_f__18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _13_1) true) true) (summary_4_function_f__18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _13_1))))


(declare-fun |block_24_function_f__18_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(block_24_function_f__18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _13_1)))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (block_24_function_f__18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _13_1) (and (summary_4_function_f__18_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_2_1 state_3 x_2_2 _13_1) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_0_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_0_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_0_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_0_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true))))))) true) (summary_5_function_f__18_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_3 x_2_2 _13_1))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (interface_0_A_19_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_5_function_f__18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _13_1) (= error_0 0))) (interface_0_A_19_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_25_constructor_10_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_26__9_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(block_25_constructor_10_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (block_25_constructor_10_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_26__9_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_27_return_constructor_10_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (block_26__9_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= x_2_2 expr_7_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_1 expr_6_0) (and (=> true (and (>= expr_5_0 0) (<= expr_5_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_5_0 x_2_1) (and (=> true true) (and (= expr_6_0 42) true)))))))) true) (block_27_return_constructor_10_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (block_27_return_constructor_10_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_3_constructor_10_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |contract_initializer_28_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_29_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) (contract_initializer_entry_29_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |contract_initializer_after_init_30_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (contract_initializer_entry_29_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (contract_initializer_after_init_30_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (contract_initializer_after_init_30_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_3_constructor_10_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (contract_initializer_28_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (contract_initializer_after_init_30_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 0) (and (summary_3_constructor_10_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))) true) (contract_initializer_28_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |implicit_constructor_entry_31_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_2_2 x_2_0))) true) (and true (= x_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_31_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (implicit_constructor_entry_31_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (contract_initializer_28_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_constructor_2_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (implicit_constructor_entry_31_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 0) (and (contract_initializer_28_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))) true) (summary_constructor_2_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int))
(=> (and (and (summary_constructor_2_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_A_19_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_32_function_f__18_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_33_f_17_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(block_32_function_f__18_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_1)))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (block_32_function_f__18_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= y_25_1 y_25_0)) (= x_2_1 x_2_0))) true) true)) true) (block_33_f_17_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_1))))


(declare-fun |block_34_return_function_f__18_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (block_33_f_17_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_1) (and (= _13_2 expr_15_0) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_2_1) (and (= _13_1 0) true))))) true) (block_34_return_function_f__18_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_2))))


(declare-fun |block_35_return_ghost_f_16_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (block_35_return_ghost_f_16_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_2) (and (= _13_2 expr_15_0) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_2_1) (and (= _13_1 0) true))))) true) (block_34_return_function_f__18_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_2))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (block_34_return_function_f__18_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_1) true) true) (summary_10_function_f__18_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_1))))


(declare-fun |block_36_function_f__18_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(block_36_function_f__18_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_1)))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (block_36_function_f__18_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_1) (and (summary_10_function_f__18_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 y_25_1 x_2_1 state_3 y_25_2 x_2_2 _13_1) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_1_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_1_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_1_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_1_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= y_25_1 y_25_0)) (= x_2_1 x_2_0))) true) true))))))) true) (summary_11_function_f__18_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_3 y_25_2 x_2_2 _13_1))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (interface_6_B_26_0 this_0 abi_0 crypto_0 state_0 y_25_0 x_2_0) true) (and (summary_11_function_f__18_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_1) (= error_0 0))) (interface_6_B_26_0 this_0 abi_0 crypto_0 state_1 y_25_1 x_2_1))))


(declare-fun |contract_initializer_37_B_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(declare-fun |contract_initializer_entry_38_B_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= y_25_1 y_25_0)) (= x_2_1 x_2_0))) (contract_initializer_entry_38_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1))))


(declare-fun |summary_39_function_f__18_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (summary_10_function_f__18_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_2) (summary_39_function_f__18_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_2))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (contract_initializer_entry_38_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1) (and (summary_39_function_f__18_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 y_25_1 x_2_1 state_1 y_25_1 x_2_1 _13_2) (and true true))) (> error_1 0)) (contract_initializer_37_B_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1))))


(declare-fun |contract_initializer_after_init_40_B_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (contract_initializer_entry_38_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1) (and (= y_25_2 expr_24_0) (and (=> true (and (>= expr_24_0 0) (<= expr_24_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_24_0 _13_2) (and (= error_1 0) (and (summary_39_function_f__18_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 y_25_1 x_2_1 state_1 y_25_1 x_2_1 _13_2) (and true true))))))) true) (contract_initializer_after_init_40_B_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_2 x_2_1))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (contract_initializer_after_init_40_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1) true) true) (contract_initializer_37_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1))))


(declare-fun |block_41_constructor_10_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_42__9_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(block_41_constructor_10_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1)))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (block_41_constructor_10_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= y_25_1 y_25_0)) (= x_2_1 x_2_0))) true) true)) true) (block_42__9_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1))))


(declare-fun |block_43_return_constructor_10_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (block_42__9_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1) (and (= x_2_2 expr_7_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_1 expr_6_0) (and (=> true (and (>= expr_5_0 0) (<= expr_5_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_5_0 x_2_1) (and (=> true true) (and (= expr_6_0 42) true)))))))) true) (block_43_return_constructor_10_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_2))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (block_43_return_constructor_10_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1) true) true) (summary_9_constructor_10_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1))))


(declare-fun |contract_initializer_44_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_45_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) (contract_initializer_entry_45_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |contract_initializer_after_init_46_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (contract_initializer_entry_45_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (contract_initializer_after_init_46_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (contract_initializer_after_init_46_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_9_constructor_10_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 y_25_1 x_2_1 state_2 y_25_2 x_2_2) true)) (> error_1 0)) (contract_initializer_44_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (contract_initializer_after_init_46_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 0) (and (summary_9_constructor_10_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 y_25_1 x_2_1 state_2 y_25_2 x_2_2) true))) true) (contract_initializer_44_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |implicit_constructor_entry_47_B_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (and (and (= state_2 state_0) (= error_1 0)) (and (and true (= y_25_2 y_25_0)) (= x_2_2 x_2_0))) (and (and true (= y_25_2 0)) (= x_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_47_B_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 y_25_0 x_2_0 y_25_2 x_2_2))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (implicit_constructor_entry_47_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1) (and (contract_initializer_44_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_constructor_8_B_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 y_25_0 x_2_0 y_25_1 x_2_2))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (implicit_constructor_entry_47_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1) (and (contract_initializer_37_B_26_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 y_25_1 x_2_2 y_25_2 x_2_3) (and (= error_1 0) (and (contract_initializer_44_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))) (> error_2 0)) (summary_constructor_8_B_26_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 y_25_0 x_2_0 y_25_2 x_2_3))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (implicit_constructor_entry_47_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1) (and (= error_2 0) (and (contract_initializer_37_B_26_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 y_25_1 x_2_2 y_25_2 x_2_3) (and (= error_1 0) (and (contract_initializer_44_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))))) true) (summary_constructor_8_B_26_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 y_25_0 x_2_0 y_25_2 x_2_3))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (summary_constructor_8_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_6_B_26_0 this_0 abi_0 crypto_0 state_1 y_25_1 x_2_1))))


(declare-fun |block_48_function_f__18_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_49_f_17_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(block_48_function_f__18_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_1)))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (block_48_function_f__18_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= y_25_1 y_25_0)) (= x_2_1 x_2_0))) true) true)) true) (block_49_f_17_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_1))))


(declare-fun |block_50_return_function_f__18_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (block_49_f_17_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_1) (and (= _13_2 expr_15_0) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_2_1) (and (= _13_1 0) true))))) true) (block_50_return_function_f__18_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_2))))


(declare-fun |block_51_return_ghost_f_16_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (block_51_return_ghost_f_16_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_2) (and (= _13_2 expr_15_0) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_2_1) (and (= _13_1 0) true))))) true) (block_50_return_function_f__18_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_2))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (block_50_return_function_f__18_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_1) true) true) (summary_16_function_f__18_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_1))))


(declare-fun |block_52_function_f__18_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(block_52_function_f__18_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_1)))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (block_52_function_f__18_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_1) (and (summary_16_function_f__18_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 y_25_1 x_2_1 state_3 y_25_2 x_2_2 _13_1) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= y_25_1 y_25_0)) (= x_2_1 x_2_0))) true) true))))))) true) (summary_17_function_f__18_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_3 y_25_2 x_2_2 _13_1))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (interface_12_C_39_0 this_0 abi_0 crypto_0 state_0 y_25_0 x_2_0) true) (and (summary_17_function_f__18_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_1) (= error_0 0))) (interface_12_C_39_0 this_0 abi_0 crypto_0 state_1 y_25_1 x_2_1))))


(declare-fun |block_53_function_g__38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_54_g_37_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(block_53_function_g__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1)))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (block_53_function_g__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= y_25_1 y_25_0)) (= x_2_1 x_2_0))) true) true)) true) (block_54_g_37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1))))


(declare-fun |block_55_return_function_g__38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_56_function_g__38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (block_54_g_37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1) (and (= expr_34_1 (= expr_32_0 expr_33_0)) (and (=> true true) (and (= expr_33_0 42) (and (=> true (and (>= expr_32_0 0) (<= expr_32_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_32_0 y_25_1) true)))))) (and (not expr_34_1) (= error_1 3))) (block_56_function_g__38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (block_56_function_g__38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1) (summary_18_function_g__38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (block_54_g_37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1) (and (= error_1 error_0) (and (= expr_34_1 (= expr_32_0 expr_33_0)) (and (=> true true) (and (= expr_33_0 42) (and (=> true (and (>= expr_32_0 0) (<= expr_32_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_32_0 y_25_1) true))))))) true) (block_55_return_function_g__38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (block_55_return_function_g__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1) true) true) (summary_18_function_g__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1))))


(declare-fun |block_57_function_g__38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(block_57_function_g__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1)))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (block_57_function_g__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1) (and (summary_18_function_g__38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 y_25_1 x_2_1 state_3 y_25_2 x_2_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_4_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_4_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_4_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_4_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3793197966)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 226)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 23)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 155)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 142)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= y_25_1 y_25_0)) (= x_2_1 x_2_0))) true) true))))))) true) (summary_19_function_g__38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_3 y_25_2 x_2_2))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (interface_12_C_39_0 this_0 abi_0 crypto_0 state_0 y_25_0 x_2_0) true) (and (summary_19_function_g__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1) (= error_0 0))) (interface_12_C_39_0 this_0 abi_0 crypto_0 state_1 y_25_1 x_2_1))))


(declare-fun |contract_initializer_58_C_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(declare-fun |contract_initializer_entry_59_C_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= y_25_1 y_25_0)) (= x_2_1 x_2_0))) (contract_initializer_entry_59_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1))))


(declare-fun |contract_initializer_after_init_60_C_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (contract_initializer_entry_59_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1) true) true) (contract_initializer_after_init_60_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (contract_initializer_after_init_60_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1) true) true) (contract_initializer_58_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1))))


(declare-fun |contract_initializer_61_B_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(declare-fun |contract_initializer_entry_62_B_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= y_25_1 y_25_0)) (= x_2_1 x_2_0))) (contract_initializer_entry_62_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1))))


(declare-fun |summary_63_function_f__18_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (summary_16_function_f__18_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_2) (summary_63_function_f__18_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1 _13_2))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (contract_initializer_entry_62_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1) (and (summary_63_function_f__18_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 y_25_1 x_2_1 state_1 y_25_1 x_2_1 _13_2) (and true true))) (> error_1 0)) (contract_initializer_61_B_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1))))


(declare-fun |contract_initializer_after_init_64_B_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (contract_initializer_entry_62_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1) (and (= y_25_2 expr_24_0) (and (=> true (and (>= expr_24_0 0) (<= expr_24_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_24_0 _13_2) (and (= error_1 0) (and (summary_63_function_f__18_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 y_25_1 x_2_1 state_1 y_25_1 x_2_1 _13_2) (and true true))))))) true) (contract_initializer_after_init_64_B_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_2 x_2_1))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (contract_initializer_after_init_64_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1) true) true) (contract_initializer_61_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1))))


(declare-fun |block_65_constructor_10_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_66__9_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(block_65_constructor_10_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1)))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (block_65_constructor_10_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= y_25_1 y_25_0)) (= x_2_1 x_2_0))) true) true)) true) (block_66__9_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1))))


(declare-fun |block_67_return_constructor_10_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (block_66__9_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1) (and (= x_2_2 expr_7_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_1 expr_6_0) (and (=> true (and (>= expr_5_0 0) (<= expr_5_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_5_0 x_2_1) (and (=> true true) (and (= expr_6_0 42) true)))))))) true) (block_67_return_constructor_10_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_2))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (block_67_return_constructor_10_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1) true) true) (summary_15_constructor_10_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1))))


(declare-fun |contract_initializer_68_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_69_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) (contract_initializer_entry_69_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |contract_initializer_after_init_70_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (contract_initializer_entry_69_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (contract_initializer_after_init_70_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (contract_initializer_after_init_70_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_15_constructor_10_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 y_25_1 x_2_1 state_2 y_25_2 x_2_2) true)) (> error_1 0)) (contract_initializer_68_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (contract_initializer_after_init_70_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 0) (and (summary_15_constructor_10_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 y_25_1 x_2_1 state_2 y_25_2 x_2_2) true))) true) (contract_initializer_68_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |implicit_constructor_entry_71_C_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (and (and (= state_2 state_0) (= error_1 0)) (and (and true (= y_25_2 y_25_0)) (= x_2_2 x_2_0))) (and (and true (= y_25_2 0)) (= x_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_71_C_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 y_25_0 x_2_0 y_25_2 x_2_2))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (implicit_constructor_entry_71_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1) (and (contract_initializer_68_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_constructor_14_C_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 y_25_0 x_2_0 y_25_1 x_2_2))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (implicit_constructor_entry_71_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1) (and (contract_initializer_61_B_26_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 y_25_1 x_2_2 y_25_2 x_2_3) (and (= error_1 0) (and (contract_initializer_68_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))) (> error_2 0)) (summary_constructor_14_C_39_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 y_25_0 x_2_0 y_25_2 x_2_3))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (implicit_constructor_entry_71_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1) (and (contract_initializer_58_C_39_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 y_25_2 x_2_3 y_25_3 x_2_4) (and (= error_2 0) (and (contract_initializer_61_B_26_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 y_25_1 x_2_2 y_25_2 x_2_3) (and (= error_1 0) (and (contract_initializer_68_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))))) (> error_3 0)) (summary_constructor_14_C_39_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 y_25_0 x_2_0 y_25_3 x_2_4))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (implicit_constructor_entry_71_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1) (and (= error_3 0) (and (contract_initializer_58_C_39_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 y_25_2 x_2_3 y_25_3 x_2_4) (and (= error_2 0) (and (contract_initializer_61_B_26_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 y_25_1 x_2_2 y_25_2 x_2_3) (and (= error_1 0) (and (contract_initializer_68_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))))))) true) (summary_constructor_14_C_39_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 y_25_0 x_2_0 y_25_3 x_2_4))))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (summary_constructor_14_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_25_0 x_2_0 y_25_1 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_12_C_39_0 this_0 abi_0 crypto_0 state_1 y_25_1 x_2_1))))


(declare-fun |error_target_5_0| () Bool)
(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> (and (and (interface_12_C_39_0 this_0 abi_0 crypto_0 state_0 y_25_0 x_2_0) true) (and (summary_19_function_g__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_25_0 x_2_0 state_1 y_25_1 x_2_1) (= error_0 3))) error_target_5_0)))


(assert
(forall ( (_13_0 Int) (_13_1 Int) (_13_2 Int) (_13_3 Int) (_13_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_15_0 Int) (expr_24_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_0_0 Int) (funds_1_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int) (y_25_0 Int) (y_25_1 Int) (y_25_2 Int) (y_25_3 Int))
(=> error_target_5_0 false)))
(check-sat)