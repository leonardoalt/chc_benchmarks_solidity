(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_A_23_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_A_23_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_A_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int))
(=> (= error_0 0) (nondet_interface_1_A_23_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_0 x_2_0))))


(declare-fun |summary_3_constructor_8_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_4_function_f__22_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |interface_5_C_52_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_6_C_52_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_7_C_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int))
(=> (= error_0 0) (nondet_interface_6_C_52_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_0 x_2_0))))


(declare-fun |summary_8_constructor_8_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_9_function_f__22_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |summary_10_constructor_51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_11_function_f__22_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |block_12_f_21_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_4_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int))
(block_11_function_f__22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _11_1)))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_4_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int))
(=> (and (and (block_11_function_f__22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _11_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_12_f_21_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _11_1))))


(declare-fun |block_13_return_function_f__22_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_4_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_12_f_21_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _11_1) (and (= _11_2 expr_19_0) (and (=> true (and (>= expr_19_0 0) (<= expr_19_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_0 x_2_2) (and (= x_2_2 expr_17_1) (and (=> true (and (>= expr_17_1 0) (<= expr_17_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_17_1 expr_16_1) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 x_2_1) (and (=> true (and (>= expr_16_1 0) (<= expr_16_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_16_1 (+ expr_14_0 expr_15_0)) (and (=> true true) (and (= expr_15_0 1) (and (=> true (and (>= expr_14_0 0) (<= expr_14_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_14_0 x_2_1) (and (= _11_1 0) true)))))))))))))))) true) (block_13_return_function_f__22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2 _11_2))))


(declare-fun |block_14_return_ghost_f_20_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_4_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_14_return_ghost_f_20_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2 _11_2) (and (= _11_2 expr_19_0) (and (=> true (and (>= expr_19_0 0) (<= expr_19_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_0 x_2_2) (and (= x_2_2 expr_17_1) (and (=> true (and (>= expr_17_1 0) (<= expr_17_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_17_1 expr_16_1) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 x_2_1) (and (=> true (and (>= expr_16_1 0) (<= expr_16_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_16_1 (+ expr_14_0 expr_15_0)) (and (=> true true) (and (= expr_15_0 1) (and (=> true (and (>= expr_14_0 0) (<= expr_14_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_14_0 x_2_1) (and (= _11_1 0) true)))))))))))))))) true) (block_13_return_function_f__22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2 _11_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_4_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_13_return_function_f__22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _11_1) true) true) (summary_4_function_f__22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _11_1))))


(declare-fun |block_15_constructor_8_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_16__7_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_4_0 Int) (_4_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(block_15_constructor_8_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1)))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_4_0 Int) (_4_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_15_constructor_8_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= _4_1 _4_0))) true)) true) (block_16__7_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1))))


(declare-fun |block_17_return_constructor_8_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_4_0 Int) (_4_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_16__7_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1) (and (and (>= _4_1 0) (<= _4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)) true) (block_17_return_constructor_8_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_4_0 Int) (_4_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_17_return_constructor_8_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1) true) true) (summary_3_constructor_8_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1))))


(declare-fun |contract_initializer_18_A_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_19_A_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_4_0 Int) (_4_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= _4_1 _4_0))) (contract_initializer_entry_19_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1))))


(declare-fun |contract_initializer_after_init_20_A_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_4_0 Int) (_4_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (contract_initializer_entry_19_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1) true) true) (contract_initializer_after_init_20_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (contract_initializer_after_init_20_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1) (and (summary_3_constructor_8_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 _4_1 state_2 x_2_2 _4_2) true)) (> error_1 0)) (contract_initializer_18_A_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_2 x_2_2 _4_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (contract_initializer_after_init_20_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1) (and (= error_1 0) (and (summary_3_constructor_8_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 _4_1 state_2 x_2_2 _4_2) true))) true) (contract_initializer_18_A_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_2 x_2_2 _4_2))))


(declare-fun |implicit_constructor_entry_21_A_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_2_2 x_2_0))) (and true (= _4_2 _4_0))) (and true (= x_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_21_A_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_2 x_2_2 _4_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (implicit_constructor_entry_21_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_2) (and (contract_initializer_18_A_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 _4_2 state_2 x_2_2 _4_3) true)) (> error_1 0)) (summary_constructor_2_A_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_2 x_2_2 _4_3))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (implicit_constructor_entry_21_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_2) (and (= error_1 0) (and (contract_initializer_18_A_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 _4_2 state_2 x_2_2 _4_3) true))) true) (summary_constructor_2_A_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_2 x_2_2 _4_3))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (summary_constructor_2_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_3) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_A_23_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_22_function_f__22_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |block_23_f_21_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_22_function_f__22_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _11_1)))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_22_function_f__22_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _11_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_23_f_21_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _11_1))))


(declare-fun |block_24_return_function_f__22_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_23_f_21_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _11_1) (and (= _11_2 expr_19_0) (and (=> true (and (>= expr_19_0 0) (<= expr_19_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_0 x_2_2) (and (= x_2_2 expr_17_1) (and (=> true (and (>= expr_17_1 0) (<= expr_17_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_17_1 expr_16_1) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 x_2_1) (and (=> true (and (>= expr_16_1 0) (<= expr_16_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_16_1 (+ expr_14_0 expr_15_0)) (and (=> true true) (and (= expr_15_0 1) (and (=> true (and (>= expr_14_0 0) (<= expr_14_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_14_0 x_2_1) (and (= _11_1 0) true)))))))))))))))) true) (block_24_return_function_f__22_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2 _11_2))))


(declare-fun |block_25_return_ghost_f_20_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_25_return_ghost_f_20_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2 _11_2) (and (= _11_2 expr_19_0) (and (=> true (and (>= expr_19_0 0) (<= expr_19_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_0 x_2_2) (and (= x_2_2 expr_17_1) (and (=> true (and (>= expr_17_1 0) (<= expr_17_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_17_1 expr_16_1) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 x_2_1) (and (=> true (and (>= expr_16_1 0) (<= expr_16_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_16_1 (+ expr_14_0 expr_15_0)) (and (=> true true) (and (= expr_15_0 1) (and (=> true (and (>= expr_14_0 0) (<= expr_14_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_14_0 x_2_1) (and (= _11_1 0) true)))))))))))))))) true) (block_24_return_function_f__22_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2 _11_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_24_return_function_f__22_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _11_1) true) true) (summary_9_function_f__22_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1 _11_1))))


(declare-fun |block_26_constructor_51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_27__50_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_26_constructor_51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_26_constructor_51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_27__50_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_28_return_constructor_51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_29_constructor_51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_27__50_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_35_1 (= expr_33_0 expr_34_0)) (and (=> true true) (and (= expr_34_0 1) (and (=> true (and (>= expr_33_0 0) (<= expr_33_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_33_0 x_2_1) true)))))) (and (not expr_35_1) (= error_1 1))) (block_29_constructor_51_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (block_29_constructor_51_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (summary_10_constructor_51_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_30_constructor_51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_27__50_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_41_1 (= expr_39_0 expr_40_0)) (and (=> true true) (and (= expr_40_0 0) (and (=> true (and (>= expr_39_0 0) (<= expr_39_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_39_0 x_2_1) (and (= error_1 error_0) (and (= expr_35_1 (= expr_33_0 expr_34_0)) (and (=> true true) (and (= expr_34_0 1) (and (=> true (and (>= expr_33_0 0) (<= expr_33_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_33_0 x_2_1) true)))))))))))) (and (not expr_41_1) (= error_2 2))) (block_30_constructor_51_52_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (block_30_constructor_51_52_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (summary_10_constructor_51_52_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_31_constructor_51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_27__50_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_47_1 (> expr_45_0 expr_46_0)) (and (=> true true) (and (= expr_46_0 2000) (and (=> true (and (>= expr_45_0 0) (<= expr_45_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_45_0 x_2_1) (and (= error_2 error_1) (and (= expr_41_1 (= expr_39_0 expr_40_0)) (and (=> true true) (and (= expr_40_0 0) (and (=> true (and (>= expr_39_0 0) (<= expr_39_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_39_0 x_2_1) (and (= error_1 error_0) (and (= expr_35_1 (= expr_33_0 expr_34_0)) (and (=> true true) (and (= expr_34_0 1) (and (=> true (and (>= expr_33_0 0) (<= expr_33_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_33_0 x_2_1) true)))))))))))))))))) (and (not expr_47_1) (= error_3 3))) (block_31_constructor_51_52_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (block_31_constructor_51_52_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (summary_10_constructor_51_52_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_27__50_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_3 error_2) (and (= expr_47_1 (> expr_45_0 expr_46_0)) (and (=> true true) (and (= expr_46_0 2000) (and (=> true (and (>= expr_45_0 0) (<= expr_45_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_45_0 x_2_1) (and (= error_2 error_1) (and (= expr_41_1 (= expr_39_0 expr_40_0)) (and (=> true true) (and (= expr_40_0 0) (and (=> true (and (>= expr_39_0 0) (<= expr_39_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_39_0 x_2_1) (and (= error_1 error_0) (and (= expr_35_1 (= expr_33_0 expr_34_0)) (and (=> true true) (and (= expr_34_0 1) (and (=> true (and (>= expr_33_0 0) (<= expr_33_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_33_0 x_2_1) true))))))))))))))))))) true) (block_28_return_constructor_51_52_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_28_return_constructor_51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_10_constructor_51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |contract_initializer_32_C_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_33_C_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) (contract_initializer_entry_33_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |contract_initializer_after_init_34_C_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_entry_33_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (contract_initializer_after_init_34_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_34_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_10_constructor_51_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (contract_initializer_32_C_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_34_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 0) (and (summary_10_constructor_51_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))) true) (contract_initializer_32_C_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_35_constructor_8_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_36__7_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_35_constructor_8_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1)))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_35_constructor_8_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= _4_1 _4_0))) true)) true) (block_36__7_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1))))


(declare-fun |block_37_return_constructor_8_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_36__7_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1) (and (and (>= _4_1 0) (<= _4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)) true) (block_37_return_constructor_8_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_37_return_constructor_8_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1) true) true) (summary_8_constructor_8_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1))))


(declare-fun |contract_initializer_38_A_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_39_A_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= _4_1 _4_0))) (contract_initializer_entry_39_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1))))


(declare-fun |contract_initializer_after_init_40_A_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_entry_39_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1) true) true) (contract_initializer_after_init_40_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_40_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1) (and (summary_8_constructor_8_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 _4_1 state_2 x_2_2 _4_2) true)) (> error_1 0)) (contract_initializer_38_A_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_2 x_2_2 _4_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_40_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_1 x_2_1 _4_1) (and (= error_1 0) (and (summary_8_constructor_8_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 _4_1 state_2 x_2_2 _4_2) true))) true) (contract_initializer_38_A_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 _4_0 state_2 x_2_2 _4_2))))


(declare-fun |implicit_constructor_entry_41_C_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_2_2 x_2_0))) true) (and true (= x_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_41_C_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |summary_42_function_f__22_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_nonpayable$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (summary_9_function_f__22_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2 _11_2) (summary_42_function_f__22_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2 _11_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_nonpayable$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (implicit_constructor_entry_41_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_42_function_f__22_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2 _11_2) (and true true))) (> error_1 0)) (summary_constructor_7_C_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_29_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_nonpayable$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (implicit_constructor_entry_41_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (contract_initializer_38_A_23_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_2_2 _4_2 state_3 x_2_3 _4_3) (and (= _4_2 expr_29_0) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_0 _11_2) (and (= error_1 0) (and (summary_42_function_f__22_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2 _11_2) (and true true)))))))) (> error_2 0)) (summary_constructor_7_C_52_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_3 x_2_3))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_29_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_nonpayable$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (implicit_constructor_entry_41_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (contract_initializer_32_C_52_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 x_2_3 state_4 x_2_4) (and (= error_2 0) (and (contract_initializer_38_A_23_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_2_2 _4_2 state_3 x_2_3 _4_3) (and (= _4_2 expr_29_0) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_0 _11_2) (and (= error_1 0) (and (summary_42_function_f__22_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2 _11_2) (and true true)))))))))) (> error_3 0)) (summary_constructor_7_C_52_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_4 x_2_4))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_29_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_nonpayable$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (implicit_constructor_entry_41_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_3 0) (and (contract_initializer_32_C_52_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 x_2_3 state_4 x_2_4) (and (= error_2 0) (and (contract_initializer_38_A_23_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_2_2 _4_2 state_3 x_2_3 _4_3) (and (= _4_2 expr_29_0) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_0 _11_2) (and (= error_1 0) (and (summary_42_function_f__22_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2 _11_2) (and true true))))))))))) true) (summary_constructor_7_C_52_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_4 x_2_4))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_29_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_nonpayable$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (summary_constructor_7_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_5_C_52_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |error_target_4_0| () Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_29_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_nonpayable$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (summary_constructor_7_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_4_0)))


(declare-fun |error_target_5_0| () Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_29_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_nonpayable$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (summary_constructor_7_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 2))) error_target_5_0)))


(declare-fun |error_target_6_0| () Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_29_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_nonpayable$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (summary_constructor_7_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 3))) error_target_6_0)))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_4_0 Int) (_4_1 Int) (_4_2 Int) (_4_3 Int) (_4_4 Int) (_4_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_17_1 Int) (expr_19_0 Int) (expr_29_0 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_nonpayable$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> error_target_6_0 false)))
(check-sat)