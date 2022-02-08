(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|tuple()| 0)) (((|tuple()|))))
(declare-fun |interface_0_I_4_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_I_4_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_I_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_I_4_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_f__3_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_4_function_f__3_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_I_4_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_f__3_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_1_I_4_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |interface_5_C_35_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_6_C_35_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_7_C_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_1 0) (nondet_interface_6_C_35_0 error_1 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_8_function_g__34_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_9_function_g__34_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_6_C_35_0 error_1 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_1 0) (summary_9_function_g__34_35_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 _i_7_0 state_2 _i_7_1))) (nondet_interface_6_C_35_0 error_2 this_0 abi_0 crypto_0 state_0 state_2))))


(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_1 Int))
(=> (and true (= error_0 0)) (summary_3_function_f__3_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_10_I_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_11_I_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_1 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_11_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_12_I_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_1 Int))
(=> (and (and (contract_initializer_entry_11_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_12_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_1 Int))
(=> (and (and (contract_initializer_after_init_12_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_10_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_13_I_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_1 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_13_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_1 Int))
(=> (and (and (implicit_constructor_entry_13_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_10_I_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_I_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_1 Int))
(=> (and (and (implicit_constructor_entry_13_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_10_I_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_I_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(declare-fun |block_14_function_g__34_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |block_15_g_33_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(block_14_function_g__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1 x_11_1)))


(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (block_14_function_g__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1 x_11_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= _i_7_1 _i_7_0))) true)) true) (block_15_g_33_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1 x_11_1))))


(declare-fun |block_16_return_function_g__34_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |nondet_call_17_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_18_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (nondet_interface_6_C_35_0 error_1 this_0 abi_0 crypto_0 state_1 state_2) (nondet_call_17_0 error_1 this_0 abi_0 crypto_0 state_1 state_2))))


(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_18_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (block_15_g_33_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1 x_11_1) (and (nondet_call_17_0 error_1 this_0 abi_0 crypto_0 state_1 state_2) (and (=> true true) (and (= expr_18_0 _i_7_1) (and (= x_11_2 expr_16_1) (and (and (>= expr_16_1 0) (<= expr_16_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_16_1 0) (<= expr_16_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_16_1 (select (|balances| state_1) expr_15_1)) (and (=> true (and (>= expr_15_1 0) (<= expr_15_1 1461501637330902918203684832716283019655932542975))) (and (= expr_15_1 expr_14_0) (and (=> true true) (and (= expr_14_0 this_0) (and (and (>= _i_7_1 0) (<= _i_7_1 1461501637330902918203684832716283019655932542975)) (and (= x_11_1 0) true)))))))))))))) (> error_1 0)) (summary_8_function_g__34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_2 _i_7_1))))


(declare-fun |block_18_function_g__34_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_18_0 Int) (expr_21_1 |tuple()|) (expr_24_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_29_1 Int) (expr_30_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (block_15_g_33_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1 x_11_1) (and (= expr_30_1 (= expr_24_0 expr_29_1)) (and (and (>= expr_29_1 0) (<= expr_29_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_29_1 0) (<= expr_29_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_1 (select (|balances| state_2) expr_28_1)) (and (=> true (and (>= expr_28_1 0) (<= expr_28_1 1461501637330902918203684832716283019655932542975))) (and (= expr_28_1 expr_27_0) (and (=> true true) (and (= expr_27_0 this_0) (and (=> true (and (>= expr_24_0 0) (<= expr_24_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_24_0 x_11_2) (and (= error_1 0) (and (nondet_call_17_0 error_1 this_0 abi_0 crypto_0 state_1 state_2) (and (=> true true) (and (= expr_18_0 _i_7_1) (and (= x_11_2 expr_16_1) (and (and (>= expr_16_1 0) (<= expr_16_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_16_1 0) (<= expr_16_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_16_1 (select (|balances| state_1) expr_15_1)) (and (=> true (and (>= expr_15_1 0) (<= expr_15_1 1461501637330902918203684832716283019655932542975))) (and (= expr_15_1 expr_14_0) (and (=> true true) (and (= expr_14_0 this_0) (and (and (>= _i_7_1 0) (<= _i_7_1 1461501637330902918203684832716283019655932542975)) (and (= x_11_1 0) true))))))))))))))))))))))))) (and (not expr_30_1) (= error_2 1))) (block_18_function_g__34_35_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_2 _i_7_1 x_11_2))))


(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_18_0 Int) (expr_21_1 |tuple()|) (expr_24_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_29_1 Int) (expr_30_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (block_18_function_g__34_35_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_2 _i_7_1 x_11_2) (summary_8_function_g__34_35_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_2 _i_7_1))))


(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_18_0 Int) (expr_21_1 |tuple()|) (expr_24_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_29_1 Int) (expr_30_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (block_15_g_33_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1 x_11_1) (and (= error_2 error_1) (and (= expr_30_1 (= expr_24_0 expr_29_1)) (and (and (>= expr_29_1 0) (<= expr_29_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_29_1 0) (<= expr_29_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_1 (select (|balances| state_2) expr_28_1)) (and (=> true (and (>= expr_28_1 0) (<= expr_28_1 1461501637330902918203684832716283019655932542975))) (and (= expr_28_1 expr_27_0) (and (=> true true) (and (= expr_27_0 this_0) (and (=> true (and (>= expr_24_0 0) (<= expr_24_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_24_0 x_11_2) (and (= error_1 0) (and (nondet_call_17_0 error_1 this_0 abi_0 crypto_0 state_1 state_2) (and (=> true true) (and (= expr_18_0 _i_7_1) (and (= x_11_2 expr_16_1) (and (and (>= expr_16_1 0) (<= expr_16_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_16_1 0) (<= expr_16_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_16_1 (select (|balances| state_1) expr_15_1)) (and (=> true (and (>= expr_15_1 0) (<= expr_15_1 1461501637330902918203684832716283019655932542975))) (and (= expr_15_1 expr_14_0) (and (=> true true) (and (= expr_14_0 this_0) (and (and (>= _i_7_1 0) (<= _i_7_1 1461501637330902918203684832716283019655932542975)) (and (= x_11_1 0) true)))))))))))))))))))))))))) true) (block_16_return_function_g__34_35_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_2 _i_7_1 x_11_2))))


(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_18_0 Int) (expr_21_1 |tuple()|) (expr_24_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_29_1 Int) (expr_30_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (block_16_return_function_g__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1 x_11_1) true) true) (summary_8_function_g__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1))))


(declare-fun |block_19_function_g__34_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_18_0 Int) (expr_21_1 |tuple()|) (expr_24_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_29_1 Int) (expr_30_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(block_19_function_g__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1 x_11_1)))


(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_18_0 Int) (expr_21_1 |tuple()|) (expr_24_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_29_1 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (block_19_function_g__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1 x_11_1) (and (summary_8_function_g__34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 _i_7_1 state_3 _i_7_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and true (= (|msg.sig| tx_0) 3403328703)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 202)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 218)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 172)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 191)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= _i_7_1 _i_7_0))) true))))))) true) (summary_9_function_g__34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_3 _i_7_2))))


(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_18_0 Int) (expr_21_1 |tuple()|) (expr_24_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_29_1 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (interface_5_C_35_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_9_function_g__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1) (= error_0 0))) (interface_5_C_35_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_20_C_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_21_C_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_18_0 Int) (expr_21_1 |tuple()|) (expr_24_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_29_1 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_21_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_22_C_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_18_0 Int) (expr_21_1 |tuple()|) (expr_24_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_29_1 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (contract_initializer_entry_21_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_22_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_18_0 Int) (expr_21_1 |tuple()|) (expr_24_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_29_1 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (contract_initializer_after_init_22_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_20_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_23_C_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_18_0 Int) (expr_21_1 |tuple()|) (expr_24_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_29_1 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_23_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_18_0 Int) (expr_21_1 |tuple()|) (expr_24_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_29_1 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (implicit_constructor_entry_23_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_20_C_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_7_C_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_18_0 Int) (expr_21_1 |tuple()|) (expr_24_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_29_1 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (implicit_constructor_entry_23_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_20_C_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_7_C_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_18_0 Int) (expr_21_1 |tuple()|) (expr_24_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_29_1 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (summary_constructor_7_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_5_C_35_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_18_0 Int) (expr_21_1 |tuple()|) (expr_24_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_29_1 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (interface_5_C_35_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_9_function_g__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_18_0 Int) (expr_21_1 |tuple()|) (expr_24_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_29_1 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> error_target_3_0 false)))
(check-sat)