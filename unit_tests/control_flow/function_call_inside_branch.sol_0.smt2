(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_40_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_C_40_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_C_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_40_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_f__21_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_4_function_f__21_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_40_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_f__21_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_1_C_40_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |summary_5_function_g__39_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_6_function_g__39_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_24_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_40_0 error_1 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_1 0) (summary_6_function_g__39_40_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 state_2 _24_1))) (nondet_interface_1_C_40_0 error_2 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |block_7_function_f__21_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_8_f_20_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_24_1 Int) (a_27_1 Int) (a_5_0 Int) (a_5_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_7_function_f__21_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_5_1)))


(assert
(forall ( (_24_1 Int) (a_27_1 Int) (a_5_0 Int) (a_5_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_function_f__21_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_5_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_8_f_20_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_5_1))))


(declare-fun |block_9_return_function_f__21_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_10_if_header_f_19_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_11_if_true_f_18_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_12_f_20_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_24_1 Int) (a_27_1 Int) (a_5_0 Int) (a_5_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_8_f_20_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_5_1) (and (= a_5_1 0) true)) true) (block_10_if_header_f_19_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_5_1))))


(assert
(forall ( (_24_1 Int) (a_27_1 Int) (a_5_0 Int) (a_5_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_3_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_10_if_header_f_19_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_5_1) (and (= expr_3_0 true) true)) expr_3_0) (block_11_if_true_f_18_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_5_1))))


(assert
(forall ( (_24_1 Int) (a_27_1 Int) (a_5_0 Int) (a_5_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_3_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_10_if_header_f_19_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_5_1) (and (= expr_3_0 true) true)) (not expr_3_0)) (block_12_f_20_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_5_1))))


(declare-fun |summary_13_function_g__39_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_24_1 Int) (_24_2 Int) (a_27_1 Int) (a_5_0 Int) (a_5_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_3_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (summary_5_function_g__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _24_2) (summary_13_function_g__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _24_2))))


(assert
(forall ( (_24_1 Int) (_24_2 Int) (a_27_1 Int) (a_5_0 Int) (a_5_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_3_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_11_if_true_f_18_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_5_1) (and (summary_13_function_g__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _24_2) (and true true))) (> error_1 0)) (summary_3_function_f__21_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_14_function_f__21_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_24_1 Int) (_24_2 Int) (a_27_1 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_3_0 Bool) (expr_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_11_if_true_f_18_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_5_1) (and (= expr_15_1 (= expr_10_0 expr_14_1)) (and (=> true (and (>= expr_14_1 0) (<= expr_14_1 1461501637330902918203684832716283019655932542975))) (and (= expr_14_1 expr_13_0) (and (=> true true) (and (= expr_13_0 0) (and (=> true (and (>= expr_10_0 0) (<= expr_10_0 1461501637330902918203684832716283019655932542975))) (and (= expr_10_0 a_5_2) (and (= a_5_2 expr_7_0) (and (=> true (and (>= expr_7_0 0) (<= expr_7_0 1461501637330902918203684832716283019655932542975))) (and (= expr_7_0 _24_2) (and (= error_1 0) (and (summary_13_function_g__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _24_2) (and true true)))))))))))))) (and (not expr_15_1) (= error_2 1))) (block_14_function_f__21_40_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_5_2))))


(assert
(forall ( (_24_1 Int) (_24_2 Int) (a_27_1 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_3_0 Bool) (expr_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (block_14_function_f__21_40_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_5_2) (summary_3_function_f__21_40_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_24_1 Int) (_24_2 Int) (a_27_1 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_3_0 Bool) (expr_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_11_if_true_f_18_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_5_1) (and (= error_2 error_1) (and (= expr_15_1 (= expr_10_0 expr_14_1)) (and (=> true (and (>= expr_14_1 0) (<= expr_14_1 1461501637330902918203684832716283019655932542975))) (and (= expr_14_1 expr_13_0) (and (=> true true) (and (= expr_13_0 0) (and (=> true (and (>= expr_10_0 0) (<= expr_10_0 1461501637330902918203684832716283019655932542975))) (and (= expr_10_0 a_5_2) (and (= a_5_2 expr_7_0) (and (=> true (and (>= expr_7_0 0) (<= expr_7_0 1461501637330902918203684832716283019655932542975))) (and (= expr_7_0 _24_2) (and (= error_1 0) (and (summary_13_function_g__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _24_2) (and true true))))))))))))))) true) (block_12_f_20_40_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_5_2))))


(assert
(forall ( (_24_1 Int) (_24_2 Int) (a_27_1 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_3_0 Bool) (expr_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12_f_20_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_5_1) true) true) (block_9_return_function_f__21_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_5_1))))


(assert
(forall ( (_24_1 Int) (_24_2 Int) (a_27_1 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_3_0 Bool) (expr_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_9_return_function_f__21_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_5_1) true) true) (summary_3_function_f__21_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_15_function_f__21_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_24_1 Int) (_24_2 Int) (a_27_1 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_3_0 Bool) (expr_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(block_15_function_f__21_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_5_1)))


(assert
(forall ( (_24_1 Int) (_24_2 Int) (a_27_1 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_3_0 Bool) (expr_7_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_15_function_f__21_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_5_1) (and (summary_3_function_f__21_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_4_function_f__21_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (_24_1 Int) (_24_2 Int) (a_27_1 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_3_0 Bool) (expr_7_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_40_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__21_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 0))) (interface_0_C_40_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_16_function_g__39_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |block_17_g_38_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_24_0 Int) (_24_1 Int) (_24_2 Int) (a_27_0 Int) (a_27_1 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_3_0 Bool) (expr_7_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(block_16_function_g__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _24_1 a_27_1)))


(assert
(forall ( (_24_0 Int) (_24_1 Int) (_24_2 Int) (a_27_0 Int) (a_27_1 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_3_0 Bool) (expr_7_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_16_function_g__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _24_1 a_27_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_17_g_38_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _24_1 a_27_1))))


(declare-fun |block_18_return_function_g__39_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_24_0 Int) (_24_1 Int) (_24_2 Int) (a_27_0 Int) (a_27_1 Int) (a_27_2 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_29_0 Int) (expr_32_0 Int) (expr_33_1 Int) (expr_34_1 Int) (expr_36_0 Int) (expr_3_0 Bool) (expr_7_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_17_g_38_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _24_1 a_27_1) (and (= _24_2 expr_36_0) (and (=> true (and (>= expr_36_0 0) (<= expr_36_0 1461501637330902918203684832716283019655932542975))) (and (= expr_36_0 a_27_2) (and (= a_27_2 expr_34_1) (and (=> true (and (>= expr_34_1 0) (<= expr_34_1 1461501637330902918203684832716283019655932542975))) (and (= expr_34_1 expr_33_1) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 1461501637330902918203684832716283019655932542975))) (and (= expr_29_0 a_27_1) (and (=> true (and (>= expr_33_1 0) (<= expr_33_1 1461501637330902918203684832716283019655932542975))) (and (= expr_33_1 expr_32_0) (and (=> true true) (and (= expr_32_0 0) (and (= _24_1 0) (and (= a_27_1 0) true))))))))))))))) true) (block_18_return_function_g__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _24_2 a_27_2))))


(declare-fun |block_19_return_ghost_g_37_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_24_0 Int) (_24_1 Int) (_24_2 Int) (a_27_0 Int) (a_27_1 Int) (a_27_2 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_29_0 Int) (expr_32_0 Int) (expr_33_1 Int) (expr_34_1 Int) (expr_36_0 Int) (expr_3_0 Bool) (expr_7_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_19_return_ghost_g_37_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _24_2 a_27_2) (and (= _24_2 expr_36_0) (and (=> true (and (>= expr_36_0 0) (<= expr_36_0 1461501637330902918203684832716283019655932542975))) (and (= expr_36_0 a_27_2) (and (= a_27_2 expr_34_1) (and (=> true (and (>= expr_34_1 0) (<= expr_34_1 1461501637330902918203684832716283019655932542975))) (and (= expr_34_1 expr_33_1) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 1461501637330902918203684832716283019655932542975))) (and (= expr_29_0 a_27_1) (and (=> true (and (>= expr_33_1 0) (<= expr_33_1 1461501637330902918203684832716283019655932542975))) (and (= expr_33_1 expr_32_0) (and (=> true true) (and (= expr_32_0 0) (and (= _24_1 0) (and (= a_27_1 0) true))))))))))))))) true) (block_18_return_function_g__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _24_2 a_27_2))))


(assert
(forall ( (_24_0 Int) (_24_1 Int) (_24_2 Int) (a_27_0 Int) (a_27_1 Int) (a_27_2 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_29_0 Int) (expr_32_0 Int) (expr_33_1 Int) (expr_34_1 Int) (expr_36_0 Int) (expr_3_0 Bool) (expr_7_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_18_return_function_g__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _24_1 a_27_1) true) true) (summary_5_function_g__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _24_1))))


(declare-fun |block_20_function_g__39_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_24_0 Int) (_24_1 Int) (_24_2 Int) (a_27_0 Int) (a_27_1 Int) (a_27_2 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_29_0 Int) (expr_32_0 Int) (expr_33_1 Int) (expr_34_1 Int) (expr_36_0 Int) (expr_3_0 Bool) (expr_7_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(block_20_function_g__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _24_1 a_27_1)))


(assert
(forall ( (_24_0 Int) (_24_1 Int) (_24_2 Int) (a_27_0 Int) (a_27_1 Int) (a_27_2 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_29_0 Int) (expr_32_0 Int) (expr_33_1 Int) (expr_34_1 Int) (expr_36_0 Int) (expr_3_0 Bool) (expr_7_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_20_function_g__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _24_1 a_27_1) (and (summary_5_function_g__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3 _24_1) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_3_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_3_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_3_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_3_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3793197966)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 226)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 23)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 155)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 142)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_6_function_g__39_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3 _24_1))))


(assert
(forall ( (_24_0 Int) (_24_1 Int) (_24_2 Int) (a_27_0 Int) (a_27_1 Int) (a_27_2 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_29_0 Int) (expr_32_0 Int) (expr_33_1 Int) (expr_34_1 Int) (expr_36_0 Int) (expr_3_0 Bool) (expr_7_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_40_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_6_function_g__39_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _24_1) (= error_0 0))) (interface_0_C_40_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_21_C_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_22_C_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_24_0 Int) (_24_1 Int) (_24_2 Int) (a_27_0 Int) (a_27_1 Int) (a_27_2 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_29_0 Int) (expr_32_0 Int) (expr_33_1 Int) (expr_34_1 Int) (expr_36_0 Int) (expr_3_0 Bool) (expr_7_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_22_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_23_C_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_24_0 Int) (_24_1 Int) (_24_2 Int) (a_27_0 Int) (a_27_1 Int) (a_27_2 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_29_0 Int) (expr_32_0 Int) (expr_33_1 Int) (expr_34_1 Int) (expr_36_0 Int) (expr_3_0 Bool) (expr_7_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_22_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_23_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_24_0 Int) (_24_1 Int) (_24_2 Int) (a_27_0 Int) (a_27_1 Int) (a_27_2 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_29_0 Int) (expr_32_0 Int) (expr_33_1 Int) (expr_34_1 Int) (expr_36_0 Int) (expr_3_0 Bool) (expr_7_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_23_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_21_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_24_C_40_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_24_0 Int) (_24_1 Int) (_24_2 Int) (a_27_0 Int) (a_27_1 Int) (a_27_2 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_29_0 Int) (expr_32_0 Int) (expr_33_1 Int) (expr_34_1 Int) (expr_36_0 Int) (expr_3_0 Bool) (expr_7_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_24_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_24_0 Int) (_24_1 Int) (_24_2 Int) (a_27_0 Int) (a_27_1 Int) (a_27_2 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_29_0 Int) (expr_32_0 Int) (expr_33_1 Int) (expr_34_1 Int) (expr_36_0 Int) (expr_3_0 Bool) (expr_7_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_24_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_21_C_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_C_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_24_0 Int) (_24_1 Int) (_24_2 Int) (a_27_0 Int) (a_27_1 Int) (a_27_2 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_29_0 Int) (expr_32_0 Int) (expr_33_1 Int) (expr_34_1 Int) (expr_36_0 Int) (expr_3_0 Bool) (expr_7_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_24_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_21_C_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_C_40_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_24_0 Int) (_24_1 Int) (_24_2 Int) (a_27_0 Int) (a_27_1 Int) (a_27_2 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_29_0 Int) (expr_32_0 Int) (expr_33_1 Int) (expr_34_1 Int) (expr_36_0 Int) (expr_3_0 Bool) (expr_7_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_2_C_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_40_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_4_0| () Bool)
(assert
(forall ( (_24_0 Int) (_24_1 Int) (_24_2 Int) (a_27_0 Int) (a_27_1 Int) (a_27_2 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_29_0 Int) (expr_32_0 Int) (expr_33_1 Int) (expr_34_1 Int) (expr_36_0 Int) (expr_3_0 Bool) (expr_7_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_40_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__21_40_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 1))) error_target_4_0)))


(assert
(forall ( (_24_0 Int) (_24_1 Int) (_24_2 Int) (a_27_0 Int) (a_27_1 Int) (a_27_2 Int) (a_5_0 Int) (a_5_1 Int) (a_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Bool) (expr_29_0 Int) (expr_32_0 Int) (expr_33_1 Int) (expr_34_1 Int) (expr_36_0 Int) (expr_3_0 Bool) (expr_7_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_4_0 false)))
(check-sat)