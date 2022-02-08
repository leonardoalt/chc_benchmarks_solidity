(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_4_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_C_4_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_C_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int))
(=> (= error_0 0) (nondet_interface_1_C_4_0 error_0 this_0 abi_0 crypto_0 state_0 x_3_0 state_0 x_3_0))))


(declare-fun |summary_3_function_test__18_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Bool ) Bool)
(declare-fun |interface_4_D_28_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_5_D_28_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_6_D_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int))
(=> (= error_0 0) (nondet_interface_5_D_28_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_7_function_test__18_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Bool ) Bool)
(declare-fun |summary_8_function_f__27_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_9_function_f__27_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int))
(=> (and (and (nondet_interface_5_D_28_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_9_function_f__27_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_5_D_28_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |block_10_function_test__18_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Bool ) Bool)
(declare-fun |block_11_test_17_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Bool ) Bool)
(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int))
(block_10_function_test__18_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1 _7_1)))


(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int))
(=> (and (and (block_10_function_test__18_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1 _7_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_11_test_17_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1 _7_1))))


(declare-fun |block_12_return_function_test__18_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Bool ) Bool)
(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int))
(=> (and (and (block_11_test_17_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1 _7_1) (and (= _7_2 expr_15_1) (and (= expr_15_1 (> expr_13_1 expr_14_0)) (and (=> true true) (and (= expr_14_0 20) (and (and (>= expr_13_1 0) (<= expr_13_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_13_1 0) (<= expr_13_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_1 (|bytes_tuple_accessor_length| expr_12_length_pair_0)) (and (= _7_1 false) true))))))))) true) (block_12_return_function_test__18_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1 _7_2))))


(declare-fun |block_13_return_ghost_test_16_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Bool ) Bool)
(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int))
(=> (and (and (block_13_return_ghost_test_16_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1 _7_2) (and (= _7_2 expr_15_1) (and (= expr_15_1 (> expr_13_1 expr_14_0)) (and (=> true true) (and (= expr_14_0 20) (and (and (>= expr_13_1 0) (<= expr_13_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_13_1 0) (<= expr_13_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_1 (|bytes_tuple_accessor_length| expr_12_length_pair_0)) (and (= _7_1 false) true))))))))) true) (block_12_return_function_test__18_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1 _7_2))))


(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int))
(=> (and (and (block_12_return_function_test__18_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1 _7_1) true) true) (summary_3_function_test__18_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1 _7_1))))


(declare-fun |contract_initializer_14_C_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_15_C_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (contract_initializer_entry_15_C_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |contract_initializer_after_init_16_C_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (contract_initializer_entry_15_C_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (= x_3_2 expr_2_0) (and (=> true true) (and (= expr_2_0 2) true)))) true) (contract_initializer_after_init_16_C_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_2))))


(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (contract_initializer_after_init_16_C_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) true) (contract_initializer_14_C_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |implicit_constructor_entry_17_C_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (and true (= x_3_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_17_C_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (implicit_constructor_entry_17_C_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (contract_initializer_14_C_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)) (> error_1 0)) (summary_constructor_2_C_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_3_0 x_3_2))))


(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (implicit_constructor_entry_17_C_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (= error_1 0) (and (contract_initializer_14_C_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true))) true) (summary_constructor_2_C_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_3_0 x_3_2))))


(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (summary_constructor_2_C_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_4_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |block_18_function_test__18_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Bool ) Bool)
(declare-fun |block_19_test_17_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Bool ) Bool)
(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_18_function_test__18_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _7_1)))


(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_18_function_test__18_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _7_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_19_test_17_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _7_1))))


(declare-fun |block_20_return_function_test__18_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Bool ) Bool)
(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_19_test_17_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _7_1) (and (= _7_2 expr_15_1) (and (= expr_15_1 (> expr_13_1 expr_14_0)) (and (=> true true) (and (= expr_14_0 20) (and (and (>= expr_13_1 0) (<= expr_13_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_13_1 0) (<= expr_13_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_1 (|bytes_tuple_accessor_length| expr_12_length_pair_0)) (and (= _7_1 false) true))))))))) true) (block_20_return_function_test__18_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _7_2))))


(declare-fun |block_21_return_ghost_test_16_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Bool ) Bool)
(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_21_return_ghost_test_16_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _7_2) (and (= _7_2 expr_15_1) (and (= expr_15_1 (> expr_13_1 expr_14_0)) (and (=> true true) (and (= expr_14_0 20) (and (and (>= expr_13_1 0) (<= expr_13_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_13_1 0) (<= expr_13_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_1 (|bytes_tuple_accessor_length| expr_12_length_pair_0)) (and (= _7_1 false) true))))))))) true) (block_20_return_function_test__18_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _7_2))))


(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_20_return_function_test__18_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _7_1) true) true) (summary_7_function_test__18_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _7_1))))


(declare-fun |block_22_function_f__27_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_23_f_26_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_22_function_f__27_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_22_function_f__27_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_23_f_26_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_24_return_function_f__27_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_25_function_test__18_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Bool ) Bool)
(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_bool_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (summary_7_function_test__18_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _7_2) (summary_25_function_test__18_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _7_2))))


(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_bool_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_23_f_26_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_25_function_test__18_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _7_2) (and true true))) (> error_1 0)) (summary_8_function_f__27_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_26_function_f__27_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_23_0 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_bool_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_23_f_26_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_23_0 _7_2) (and (= error_1 0) (and (summary_25_function_test__18_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _7_2) (and true true))))) (and (not expr_23_0) (= error_2 1))) (block_26_function_f__27_28_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_23_0 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_bool_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (block_26_function_f__27_28_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_8_function_f__27_28_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_23_0 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_bool_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_23_f_26_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_2 error_1) (and (= expr_23_0 _7_2) (and (= error_1 0) (and (summary_25_function_test__18_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _7_2) (and true true)))))) true) (block_24_return_function_f__27_28_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_23_0 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_bool_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_24_return_function_f__27_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (summary_8_function_f__27_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_27_function_f__27_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_23_0 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_bool_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_27_function_f__27_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_23_0 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bool_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_27_function_f__27_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_8_function_f__27_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_9_function_f__27_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_23_0 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bool_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (interface_4_D_28_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_9_function_f__27_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 0))) (interface_4_D_28_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_28_D_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_29_D_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_23_0 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bool_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_29_D_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_30_D_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_23_0 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bool_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_entry_29_D_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_30_D_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_23_0 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bool_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_30_D_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_28_D_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_31_D_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_23_0 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bool_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_31_D_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_23_0 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bool_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_31_D_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_28_D_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_6_D_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_23_0 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bool_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_31_D_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_28_D_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_6_D_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_23_0 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bool_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (summary_constructor_6_D_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_4_D_28_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_23_0 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bool_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (interface_4_D_28_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_9_function_f__27_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (_7_0 Bool) (_7_1 Bool) (_7_2 Bool) (_7_3 Bool) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_length_pair_0 |bytes_tuple|) (expr_13_1 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_23_0 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bool_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> error_target_3_0 false)))
(check-sat)