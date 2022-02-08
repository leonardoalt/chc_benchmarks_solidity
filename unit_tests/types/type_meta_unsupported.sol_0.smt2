(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_A_1_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_A_1_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_A_1_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_A_1_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |interface_3_C_39_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_4_C_39_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_5_C_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_4_C_39_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_6_function_f__38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_7_function_f__38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_4_C_39_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_7_function_f__38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_4_C_39_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |contract_initializer_8_A_1_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_9_A_1_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_9_A_1_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_10_A_1_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_9_A_1_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_10_A_1_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_10_A_1_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_8_A_1_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_11_A_1_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_11_A_1_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_11_A_1_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_8_A_1_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_A_1_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_11_A_1_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_8_A_1_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_A_1_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_2_A_1_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_A_1_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_12_function_f__38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_13_f_37_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_12_function_f__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12_function_f__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_13_f_37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_14_return_function_f__38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_15_function_f__38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_length_pair_0 |bytes_tuple|) (expr_11_length_pair_0 |bytes_tuple|) (expr_11_length_pair_1 |bytes_tuple|) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_13_f_37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_14_1 (not (= expr_12_1 expr_13_0))) (and (=> true true) (and (= expr_13_0 0) (and (and (>= expr_12_1 0) (<= expr_12_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_12_1 0) (<= expr_12_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_12_1 (|bytes_tuple_accessor_length| expr_11_length_pair_1)) (and (= expr_11_length_pair_1 expr_10_length_pair_0) true)))))))) (and (not expr_14_1) (= error_1 1))) (block_15_function_f__38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_length_pair_0 |bytes_tuple|) (expr_11_length_pair_0 |bytes_tuple|) (expr_11_length_pair_1 |bytes_tuple|) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_15_function_f__38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_6_function_f__38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_16_function_f__38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_length_pair_0 |bytes_tuple|) (expr_11_length_pair_0 |bytes_tuple|) (expr_11_length_pair_1 |bytes_tuple|) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_21_length_pair_0 |bytes_tuple|) (expr_22_1 Int) (expr_23_0 Int) (expr_24_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_13_f_37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_24_1 (not (= expr_22_1 expr_23_0))) (and (=> true true) (and (= expr_23_0 0) (and (and (>= expr_22_1 0) (<= expr_22_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_22_1 0) (<= expr_22_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_1 (|bytes_tuple_accessor_length| expr_21_length_pair_0)) (and (= error_1 error_0) (and (= expr_14_1 (not (= expr_12_1 expr_13_0))) (and (=> true true) (and (= expr_13_0 0) (and (and (>= expr_12_1 0) (<= expr_12_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_12_1 0) (<= expr_12_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_12_1 (|bytes_tuple_accessor_length| expr_11_length_pair_1)) (and (= expr_11_length_pair_1 expr_10_length_pair_0) true))))))))))))))) (and (not expr_24_1) (= error_2 2))) (block_16_function_f__38_39_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_length_pair_0 |bytes_tuple|) (expr_11_length_pair_0 |bytes_tuple|) (expr_11_length_pair_1 |bytes_tuple|) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_21_length_pair_0 |bytes_tuple|) (expr_22_1 Int) (expr_23_0 Int) (expr_24_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_16_function_f__38_39_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_6_function_f__38_39_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_17_function_f__38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_length_pair_0 |bytes_tuple|) (expr_11_length_pair_0 |bytes_tuple|) (expr_11_length_pair_1 |bytes_tuple|) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_21_length_pair_0 |bytes_tuple|) (expr_22_1 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_31_length_pair_0 |bytes_tuple|) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_13_f_37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_34_1 (not (= expr_32_1 expr_33_0))) (and (=> true true) (and (= expr_33_0 0) (and (and (>= expr_32_1 0) (<= expr_32_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_32_1 0) (<= expr_32_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_32_1 (|bytes_tuple_accessor_length| expr_31_length_pair_0)) (and (= error_2 error_1) (and (= expr_24_1 (not (= expr_22_1 expr_23_0))) (and (=> true true) (and (= expr_23_0 0) (and (and (>= expr_22_1 0) (<= expr_22_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_22_1 0) (<= expr_22_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_1 (|bytes_tuple_accessor_length| expr_21_length_pair_0)) (and (= error_1 error_0) (and (= expr_14_1 (not (= expr_12_1 expr_13_0))) (and (=> true true) (and (= expr_13_0 0) (and (and (>= expr_12_1 0) (<= expr_12_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_12_1 0) (<= expr_12_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_12_1 (|bytes_tuple_accessor_length| expr_11_length_pair_1)) (and (= expr_11_length_pair_1 expr_10_length_pair_0) true)))))))))))))))))))))) (and (not expr_34_1) (= error_3 3))) (block_17_function_f__38_39_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_length_pair_0 |bytes_tuple|) (expr_11_length_pair_0 |bytes_tuple|) (expr_11_length_pair_1 |bytes_tuple|) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_21_length_pair_0 |bytes_tuple|) (expr_22_1 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_31_length_pair_0 |bytes_tuple|) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_17_function_f__38_39_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_6_function_f__38_39_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_length_pair_0 |bytes_tuple|) (expr_11_length_pair_0 |bytes_tuple|) (expr_11_length_pair_1 |bytes_tuple|) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_21_length_pair_0 |bytes_tuple|) (expr_22_1 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_31_length_pair_0 |bytes_tuple|) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_13_f_37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_3 error_2) (and (= expr_34_1 (not (= expr_32_1 expr_33_0))) (and (=> true true) (and (= expr_33_0 0) (and (and (>= expr_32_1 0) (<= expr_32_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_32_1 0) (<= expr_32_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_32_1 (|bytes_tuple_accessor_length| expr_31_length_pair_0)) (and (= error_2 error_1) (and (= expr_24_1 (not (= expr_22_1 expr_23_0))) (and (=> true true) (and (= expr_23_0 0) (and (and (>= expr_22_1 0) (<= expr_22_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_22_1 0) (<= expr_22_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_1 (|bytes_tuple_accessor_length| expr_21_length_pair_0)) (and (= error_1 error_0) (and (= expr_14_1 (not (= expr_12_1 expr_13_0))) (and (=> true true) (and (= expr_13_0 0) (and (and (>= expr_12_1 0) (<= expr_12_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_12_1 0) (<= expr_12_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_12_1 (|bytes_tuple_accessor_length| expr_11_length_pair_1)) (and (= expr_11_length_pair_1 expr_10_length_pair_0) true))))))))))))))))))))))) true) (block_14_return_function_f__38_39_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_length_pair_0 |bytes_tuple|) (expr_11_length_pair_0 |bytes_tuple|) (expr_11_length_pair_1 |bytes_tuple|) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_21_length_pair_0 |bytes_tuple|) (expr_22_1 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_31_length_pair_0 |bytes_tuple|) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_14_return_function_f__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (summary_6_function_f__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_18_function_f__38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_length_pair_0 |bytes_tuple|) (expr_11_length_pair_0 |bytes_tuple|) (expr_11_length_pair_1 |bytes_tuple|) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_21_length_pair_0 |bytes_tuple|) (expr_22_1 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_31_length_pair_0 |bytes_tuple|) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_18_function_f__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_length_pair_0 |bytes_tuple|) (expr_11_length_pair_0 |bytes_tuple|) (expr_11_length_pair_1 |bytes_tuple|) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_21_length_pair_0 |bytes_tuple|) (expr_22_1 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_31_length_pair_0 |bytes_tuple|) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_18_function_f__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_6_function_f__38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_4_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_4_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_4_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_4_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_7_function_f__38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_length_pair_0 |bytes_tuple|) (expr_11_length_pair_0 |bytes_tuple|) (expr_11_length_pair_1 |bytes_tuple|) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_21_length_pair_0 |bytes_tuple|) (expr_22_1 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_31_length_pair_0 |bytes_tuple|) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_3_C_39_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_7_function_f__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 0))) (interface_3_C_39_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_19_C_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_20_C_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_length_pair_0 |bytes_tuple|) (expr_11_length_pair_0 |bytes_tuple|) (expr_11_length_pair_1 |bytes_tuple|) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_21_length_pair_0 |bytes_tuple|) (expr_22_1 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_31_length_pair_0 |bytes_tuple|) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_20_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_21_C_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_length_pair_0 |bytes_tuple|) (expr_11_length_pair_0 |bytes_tuple|) (expr_11_length_pair_1 |bytes_tuple|) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_21_length_pair_0 |bytes_tuple|) (expr_22_1 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_31_length_pair_0 |bytes_tuple|) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_20_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_21_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_length_pair_0 |bytes_tuple|) (expr_11_length_pair_0 |bytes_tuple|) (expr_11_length_pair_1 |bytes_tuple|) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_21_length_pair_0 |bytes_tuple|) (expr_22_1 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_31_length_pair_0 |bytes_tuple|) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_21_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_19_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_22_C_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_length_pair_0 |bytes_tuple|) (expr_11_length_pair_0 |bytes_tuple|) (expr_11_length_pair_1 |bytes_tuple|) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_21_length_pair_0 |bytes_tuple|) (expr_22_1 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_31_length_pair_0 |bytes_tuple|) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_22_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_length_pair_0 |bytes_tuple|) (expr_11_length_pair_0 |bytes_tuple|) (expr_11_length_pair_1 |bytes_tuple|) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_21_length_pair_0 |bytes_tuple|) (expr_22_1 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_31_length_pair_0 |bytes_tuple|) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_22_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_19_C_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_5_C_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_length_pair_0 |bytes_tuple|) (expr_11_length_pair_0 |bytes_tuple|) (expr_11_length_pair_1 |bytes_tuple|) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_21_length_pair_0 |bytes_tuple|) (expr_22_1 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_31_length_pair_0 |bytes_tuple|) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_22_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_19_C_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_5_C_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_length_pair_0 |bytes_tuple|) (expr_11_length_pair_0 |bytes_tuple|) (expr_11_length_pair_1 |bytes_tuple|) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_21_length_pair_0 |bytes_tuple|) (expr_22_1 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_31_length_pair_0 |bytes_tuple|) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_5_C_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_3_C_39_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_5_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_length_pair_0 |bytes_tuple|) (expr_11_length_pair_0 |bytes_tuple|) (expr_11_length_pair_1 |bytes_tuple|) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_21_length_pair_0 |bytes_tuple|) (expr_22_1 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_31_length_pair_0 |bytes_tuple|) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_3_C_39_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_7_function_f__38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 1))) error_target_5_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_length_pair_0 |bytes_tuple|) (expr_11_length_pair_0 |bytes_tuple|) (expr_11_length_pair_1 |bytes_tuple|) (expr_12_1 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_21_length_pair_0 |bytes_tuple|) (expr_22_1 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_31_length_pair_0 |bytes_tuple|) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_5_0 false)))
(check-sat)