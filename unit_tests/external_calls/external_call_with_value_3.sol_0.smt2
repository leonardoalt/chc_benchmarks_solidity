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


(declare-fun |interface_5_C_49_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_6_C_49_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_7_C_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_1 0) (nondet_interface_6_C_49_0 error_1 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_8_function_g__48_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_9_function_g__48_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (i_7_0 Int) (i_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_6_C_49_0 error_1 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_1 0) (summary_9_function_g__48_49_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 i_7_0 state_2 i_7_1))) (nondet_interface_6_C_49_0 error_2 this_0 abi_0 crypto_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (i_7_0 Int) (i_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and true (= error_0 0)) (summary_3_function_f__3_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_10_I_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_11_I_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (i_7_0 Int) (i_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_11_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_12_I_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (i_7_0 Int) (i_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_11_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_12_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (i_7_0 Int) (i_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_12_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_10_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_13_I_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (i_7_0 Int) (i_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_13_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (i_7_0 Int) (i_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_13_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_10_I_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_I_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (i_7_0 Int) (i_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_13_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_10_I_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_I_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(declare-fun |block_14_function_g__48_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_15_g_47_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_14_function_g__48_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_1 i_7_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_14_function_g__48_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_1 i_7_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= i_7_1 i_7_0))) true)) true) (block_15_g_47_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_1 i_7_1))))


(declare-fun |block_16_return_function_g__48_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |nondet_call_17_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_20_0 Int) (expr_23_0 Int) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (nondet_interface_6_C_49_0 error_1 this_0 abi_0 crypto_0 state_2 state_3) (nondet_call_17_0 error_1 this_0 abi_0 crypto_0 state_2 state_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_20_0 Int) (expr_23_0 Int) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_15_g_47_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_1 i_7_1) (and (nondet_call_17_0 error_1 this_0 abi_0 crypto_0 state_2 state_3) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) (- 0 expr_23_0))))) (and (=> true true) (and (= expr_23_0 20) (and (=> true true) (and (= expr_20_0 i_7_1) (and (=> true expr_17_1) (and (= expr_17_1 (> expr_15_1 expr_16_0)) (and (=> true true) (and (= expr_16_0 100) (and (and (>= expr_15_1 0) (<= expr_15_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_15_1 0) (<= expr_15_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_1 (select (|balances| state_1) expr_14_1)) (and (=> true (and (>= expr_14_1 0) (<= expr_14_1 1461501637330902918203684832716283019655932542975))) (and (= expr_14_1 expr_13_0) (and (=> true true) (and (= expr_13_0 this_0) (and (and (>= i_7_1 0) (<= i_7_1 1461501637330902918203684832716283019655932542975)) true))))))))))))))))))) (> error_1 0)) (summary_8_function_g__48_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_3 i_7_1))))


(declare-fun |block_18_function_g__48_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_20_0 Int) (expr_23_0 Int) (expr_25_1 |tuple()|) (expr_30_0 Int) (expr_31_1 Int) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_15_g_47_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_1 i_7_1) (and (= expr_34_1 (> expr_32_1 expr_33_0)) (and (=> true true) (and (= expr_33_0 0) (and (and (>= expr_32_1 0) (<= expr_32_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_32_1 0) (<= expr_32_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_32_1 (select (|balances| state_3) expr_31_1)) (and (=> true (and (>= expr_31_1 0) (<= expr_31_1 1461501637330902918203684832716283019655932542975))) (and (= expr_31_1 expr_30_0) (and (=> true true) (and (= expr_30_0 this_0) (and (= error_1 0) (and (nondet_call_17_0 error_1 this_0 abi_0 crypto_0 state_2 state_3) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) (- 0 expr_23_0))))) (and (=> true true) (and (= expr_23_0 20) (and (=> true true) (and (= expr_20_0 i_7_1) (and (=> true expr_17_1) (and (= expr_17_1 (> expr_15_1 expr_16_0)) (and (=> true true) (and (= expr_16_0 100) (and (and (>= expr_15_1 0) (<= expr_15_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_15_1 0) (<= expr_15_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_1 (select (|balances| state_1) expr_14_1)) (and (=> true (and (>= expr_14_1 0) (<= expr_14_1 1461501637330902918203684832716283019655932542975))) (and (= expr_14_1 expr_13_0) (and (=> true true) (and (= expr_13_0 this_0) (and (and (>= i_7_1 0) (<= i_7_1 1461501637330902918203684832716283019655932542975)) true)))))))))))))))))))))))))))))) (and (not expr_34_1) (= error_2 1))) (block_18_function_g__48_49_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_3 i_7_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_20_0 Int) (expr_23_0 Int) (expr_25_1 |tuple()|) (expr_30_0 Int) (expr_31_1 Int) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_18_function_g__48_49_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_3 i_7_1) (summary_8_function_g__48_49_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_3 i_7_1))))


(declare-fun |block_19_function_g__48_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_20_0 Int) (expr_23_0 Int) (expr_25_1 |tuple()|) (expr_30_0 Int) (expr_31_1 Int) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_1 Int) (expr_42_1 Int) (expr_43_0 Int) (expr_44_1 Bool) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_15_g_47_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_1 i_7_1) (and (= expr_44_1 (= expr_42_1 expr_43_0)) (and (=> true true) (and (= expr_43_0 0) (and (and (>= expr_42_1 0) (<= expr_42_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_42_1 0) (<= expr_42_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_42_1 (select (|balances| state_3) expr_41_1)) (and (=> true (and (>= expr_41_1 0) (<= expr_41_1 1461501637330902918203684832716283019655932542975))) (and (= expr_41_1 expr_40_0) (and (=> true true) (and (= expr_40_0 this_0) (and (= error_2 error_1) (and (= expr_34_1 (> expr_32_1 expr_33_0)) (and (=> true true) (and (= expr_33_0 0) (and (and (>= expr_32_1 0) (<= expr_32_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_32_1 0) (<= expr_32_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_32_1 (select (|balances| state_3) expr_31_1)) (and (=> true (and (>= expr_31_1 0) (<= expr_31_1 1461501637330902918203684832716283019655932542975))) (and (= expr_31_1 expr_30_0) (and (=> true true) (and (= expr_30_0 this_0) (and (= error_1 0) (and (nondet_call_17_0 error_1 this_0 abi_0 crypto_0 state_2 state_3) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) (- 0 expr_23_0))))) (and (=> true true) (and (= expr_23_0 20) (and (=> true true) (and (= expr_20_0 i_7_1) (and (=> true expr_17_1) (and (= expr_17_1 (> expr_15_1 expr_16_0)) (and (=> true true) (and (= expr_16_0 100) (and (and (>= expr_15_1 0) (<= expr_15_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_15_1 0) (<= expr_15_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_1 (select (|balances| state_1) expr_14_1)) (and (=> true (and (>= expr_14_1 0) (<= expr_14_1 1461501637330902918203684832716283019655932542975))) (and (= expr_14_1 expr_13_0) (and (=> true true) (and (= expr_13_0 this_0) (and (and (>= i_7_1 0) (<= i_7_1 1461501637330902918203684832716283019655932542975)) true))))))))))))))))))))))))))))))))))))))))) (and (not expr_44_1) (= error_3 2))) (block_19_function_g__48_49_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_3 i_7_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_20_0 Int) (expr_23_0 Int) (expr_25_1 |tuple()|) (expr_30_0 Int) (expr_31_1 Int) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_1 Int) (expr_42_1 Int) (expr_43_0 Int) (expr_44_1 Bool) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_19_function_g__48_49_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_3 i_7_1) (summary_8_function_g__48_49_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_3 i_7_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_20_0 Int) (expr_23_0 Int) (expr_25_1 |tuple()|) (expr_30_0 Int) (expr_31_1 Int) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_1 Int) (expr_42_1 Int) (expr_43_0 Int) (expr_44_1 Bool) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_15_g_47_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_1 i_7_1) (and (= error_3 error_2) (and (= expr_44_1 (= expr_42_1 expr_43_0)) (and (=> true true) (and (= expr_43_0 0) (and (and (>= expr_42_1 0) (<= expr_42_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_42_1 0) (<= expr_42_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_42_1 (select (|balances| state_3) expr_41_1)) (and (=> true (and (>= expr_41_1 0) (<= expr_41_1 1461501637330902918203684832716283019655932542975))) (and (= expr_41_1 expr_40_0) (and (=> true true) (and (= expr_40_0 this_0) (and (= error_2 error_1) (and (= expr_34_1 (> expr_32_1 expr_33_0)) (and (=> true true) (and (= expr_33_0 0) (and (and (>= expr_32_1 0) (<= expr_32_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_32_1 0) (<= expr_32_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_32_1 (select (|balances| state_3) expr_31_1)) (and (=> true (and (>= expr_31_1 0) (<= expr_31_1 1461501637330902918203684832716283019655932542975))) (and (= expr_31_1 expr_30_0) (and (=> true true) (and (= expr_30_0 this_0) (and (= error_1 0) (and (nondet_call_17_0 error_1 this_0 abi_0 crypto_0 state_2 state_3) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) (- 0 expr_23_0))))) (and (=> true true) (and (= expr_23_0 20) (and (=> true true) (and (= expr_20_0 i_7_1) (and (=> true expr_17_1) (and (= expr_17_1 (> expr_15_1 expr_16_0)) (and (=> true true) (and (= expr_16_0 100) (and (and (>= expr_15_1 0) (<= expr_15_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_15_1 0) (<= expr_15_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_1 (select (|balances| state_1) expr_14_1)) (and (=> true (and (>= expr_14_1 0) (<= expr_14_1 1461501637330902918203684832716283019655932542975))) (and (= expr_14_1 expr_13_0) (and (=> true true) (and (= expr_13_0 this_0) (and (and (>= i_7_1 0) (<= i_7_1 1461501637330902918203684832716283019655932542975)) true)))))))))))))))))))))))))))))))))))))))))) true) (block_16_return_function_g__48_49_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_3 i_7_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_20_0 Int) (expr_23_0 Int) (expr_25_1 |tuple()|) (expr_30_0 Int) (expr_31_1 Int) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_1 Int) (expr_42_1 Int) (expr_43_0 Int) (expr_44_1 Bool) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_16_return_function_g__48_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_1 i_7_1) true) true) (summary_8_function_g__48_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_1 i_7_1))))


(declare-fun |block_20_function_g__48_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_20_0 Int) (expr_23_0 Int) (expr_25_1 |tuple()|) (expr_30_0 Int) (expr_31_1 Int) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_1 Int) (expr_42_1 Int) (expr_43_0 Int) (expr_44_1 Bool) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_20_function_g__48_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_1 i_7_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_20_0 Int) (expr_23_0 Int) (expr_25_1 |tuple()|) (expr_30_0 Int) (expr_31_1 Int) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_1 Int) (expr_42_1 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_20_function_g__48_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_1 i_7_1) (and (summary_8_function_g__48_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 i_7_1 state_3 i_7_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_3_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_3_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_3_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_3_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3403328703)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 202)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 218)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 172)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 191)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= i_7_1 i_7_0))) true))))))) true) (summary_9_function_g__48_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_3 i_7_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_20_0 Int) (expr_23_0 Int) (expr_25_1 |tuple()|) (expr_30_0 Int) (expr_31_1 Int) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_1 Int) (expr_42_1 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_5_C_49_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_9_function_g__48_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_1 i_7_1) (= error_0 0))) (interface_5_C_49_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_21_C_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_22_C_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_20_0 Int) (expr_23_0 Int) (expr_25_1 |tuple()|) (expr_30_0 Int) (expr_31_1 Int) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_1 Int) (expr_42_1 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_22_C_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_23_C_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_20_0 Int) (expr_23_0 Int) (expr_25_1 |tuple()|) (expr_30_0 Int) (expr_31_1 Int) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_1 Int) (expr_42_1 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_22_C_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_23_C_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_20_0 Int) (expr_23_0 Int) (expr_25_1 |tuple()|) (expr_30_0 Int) (expr_31_1 Int) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_1 Int) (expr_42_1 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_23_C_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_21_C_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_24_C_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_20_0 Int) (expr_23_0 Int) (expr_25_1 |tuple()|) (expr_30_0 Int) (expr_31_1 Int) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_1 Int) (expr_42_1 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_24_C_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_20_0 Int) (expr_23_0 Int) (expr_25_1 |tuple()|) (expr_30_0 Int) (expr_31_1 Int) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_1 Int) (expr_42_1 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_24_C_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_21_C_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_7_C_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_20_0 Int) (expr_23_0 Int) (expr_25_1 |tuple()|) (expr_30_0 Int) (expr_31_1 Int) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_1 Int) (expr_42_1 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_24_C_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_21_C_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_7_C_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_20_0 Int) (expr_23_0 Int) (expr_25_1 |tuple()|) (expr_30_0 Int) (expr_31_1 Int) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_1 Int) (expr_42_1 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_7_C_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_5_C_49_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_4_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_20_0 Int) (expr_23_0 Int) (expr_25_1 |tuple()|) (expr_30_0 Int) (expr_31_1 Int) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_1 Int) (expr_42_1 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_5_C_49_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_9_function_g__48_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_1 i_7_1) (= error_0 1))) error_target_4_0)))


(declare-fun |error_target_5_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_20_0 Int) (expr_23_0 Int) (expr_25_1 |tuple()|) (expr_30_0 Int) (expr_31_1 Int) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_1 Int) (expr_42_1 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_5_C_49_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_9_function_g__48_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 i_7_0 state_1 i_7_1) (= error_0 2))) error_target_5_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_14_1 Int) (expr_15_1 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_20_0 Int) (expr_23_0 Int) (expr_25_1 |tuple()|) (expr_30_0 Int) (expr_31_1 Int) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_40_0 Int) (expr_41_1 Int) (expr_42_1 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (i_7_0 Int) (i_7_1 Int) (i_7_2 Int) (i_7_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_5_0 false)))
(check-sat)