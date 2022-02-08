(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|struct C.S| 0)) (((|struct C.S| (|struct C.S_accessor_x| Int) (|struct C.S_accessor_d| Int)))))
(declare-fun |interface_0_C_33_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_C_33_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_C_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_33_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_f__32_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(declare-fun |summary_4_function_f__32_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (s_13_0 |struct C.S|) (s_13_1 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_33_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_f__32_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 s_13_0 state_2 s_13_1))) (nondet_interface_1_C_33_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |block_5_function_f__32_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(declare-fun |block_6_f_31_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (s_13_0 |struct C.S|) (s_13_1 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_5_function_f__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_13_0 state_1 s_13_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (s_13_0 |struct C.S|) (s_13_1 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_5_function_f__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_13_0 state_1 s_13_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= s_13_1 s_13_0))) true)) true) (block_6_f_31_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_13_0 state_1 s_13_1))))


(declare-fun |block_7_return_function_f__32_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(declare-fun |block_8_function_f__32_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_16_0 |struct C.S|) (expr_16_1 |struct C.S|) (expr_16_2 |struct C.S|) (expr_16_3 |struct C.S|) (expr_18_1 Int) (expr_18_2 Int) (expr_20_1 Int) (expr_21_1 Int) (expr_24_0 |struct C.S|) (expr_25_1 Int) (expr_27_1 Int) (expr_28_1 Bool) (s_13_0 |struct C.S|) (s_13_1 |struct C.S|) (s_13_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_6_f_31_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_13_0 state_1 s_13_1) (and (= expr_28_1 (= expr_25_1 expr_27_1)) (and (=> true (and (>= expr_27_1 0) (<= expr_27_1 1))) (and (= expr_27_1 0) (and (=> true (and (>= expr_25_1 0) (<= expr_25_1 1))) (and (= expr_25_1 (|struct C.S_accessor_d| expr_24_0)) (and (= expr_24_0 s_13_2) (and (= expr_16_3 s_13_2) (and (= s_13_2 expr_16_2) (and (=> true (and (>= expr_18_2 0) (<= expr_18_2 1))) (and (= expr_18_2 (|struct C.S_accessor_d| expr_16_2)) (and (= (|struct C.S_accessor_d| expr_16_2) expr_21_1) (and (= (|struct C.S_accessor_x| expr_16_2) (|struct C.S_accessor_x| expr_16_1)) (and (= expr_16_1 s_13_1) (and (=> true (and (>= expr_21_1 0) (<= expr_21_1 1))) (and (= expr_21_1 expr_20_1) (and (=> true (and (>= expr_18_1 0) (<= expr_18_1 1))) (and (= expr_18_1 (|struct C.S_accessor_d| expr_16_0)) (and (= expr_16_0 s_13_1) (and (=> true (and (>= expr_20_1 0) (<= expr_20_1 1))) (and (= expr_20_1 0) (and true true)))))))))))))))))))))) (and (not expr_28_1) (= error_1 1))) (block_8_function_f__32_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 s_13_0 state_1 s_13_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_16_0 |struct C.S|) (expr_16_1 |struct C.S|) (expr_16_2 |struct C.S|) (expr_16_3 |struct C.S|) (expr_18_1 Int) (expr_18_2 Int) (expr_20_1 Int) (expr_21_1 Int) (expr_24_0 |struct C.S|) (expr_25_1 Int) (expr_27_1 Int) (expr_28_1 Bool) (s_13_0 |struct C.S|) (s_13_1 |struct C.S|) (s_13_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_8_function_f__32_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 s_13_0 state_1 s_13_2) (summary_3_function_f__32_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 s_13_0 state_1 s_13_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_16_0 |struct C.S|) (expr_16_1 |struct C.S|) (expr_16_2 |struct C.S|) (expr_16_3 |struct C.S|) (expr_18_1 Int) (expr_18_2 Int) (expr_20_1 Int) (expr_21_1 Int) (expr_24_0 |struct C.S|) (expr_25_1 Int) (expr_27_1 Int) (expr_28_1 Bool) (s_13_0 |struct C.S|) (s_13_1 |struct C.S|) (s_13_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_6_f_31_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_13_0 state_1 s_13_1) (and (= error_1 error_0) (and (= expr_28_1 (= expr_25_1 expr_27_1)) (and (=> true (and (>= expr_27_1 0) (<= expr_27_1 1))) (and (= expr_27_1 0) (and (=> true (and (>= expr_25_1 0) (<= expr_25_1 1))) (and (= expr_25_1 (|struct C.S_accessor_d| expr_24_0)) (and (= expr_24_0 s_13_2) (and (= expr_16_3 s_13_2) (and (= s_13_2 expr_16_2) (and (=> true (and (>= expr_18_2 0) (<= expr_18_2 1))) (and (= expr_18_2 (|struct C.S_accessor_d| expr_16_2)) (and (= (|struct C.S_accessor_d| expr_16_2) expr_21_1) (and (= (|struct C.S_accessor_x| expr_16_2) (|struct C.S_accessor_x| expr_16_1)) (and (= expr_16_1 s_13_1) (and (=> true (and (>= expr_21_1 0) (<= expr_21_1 1))) (and (= expr_21_1 expr_20_1) (and (=> true (and (>= expr_18_1 0) (<= expr_18_1 1))) (and (= expr_18_1 (|struct C.S_accessor_d| expr_16_0)) (and (= expr_16_0 s_13_1) (and (=> true (and (>= expr_20_1 0) (<= expr_20_1 1))) (and (= expr_20_1 0) (and true true))))))))))))))))))))))) true) (block_7_return_function_f__32_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 s_13_0 state_1 s_13_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_16_0 |struct C.S|) (expr_16_1 |struct C.S|) (expr_16_2 |struct C.S|) (expr_16_3 |struct C.S|) (expr_18_1 Int) (expr_18_2 Int) (expr_20_1 Int) (expr_21_1 Int) (expr_24_0 |struct C.S|) (expr_25_1 Int) (expr_27_1 Int) (expr_28_1 Bool) (s_13_0 |struct C.S|) (s_13_1 |struct C.S|) (s_13_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_return_function_f__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_13_0 state_1 s_13_1) true) true) (summary_3_function_f__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_13_0 state_1 s_13_1))))


(declare-fun |block_9_function_f__32_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_16_0 |struct C.S|) (expr_16_1 |struct C.S|) (expr_16_2 |struct C.S|) (expr_16_3 |struct C.S|) (expr_18_1 Int) (expr_18_2 Int) (expr_20_1 Int) (expr_21_1 Int) (expr_24_0 |struct C.S|) (expr_25_1 Int) (expr_27_1 Int) (expr_28_1 Bool) (s_13_0 |struct C.S|) (s_13_1 |struct C.S|) (s_13_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_9_function_f__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_13_0 state_1 s_13_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_16_0 |struct C.S|) (expr_16_1 |struct C.S|) (expr_16_2 |struct C.S|) (expr_16_3 |struct C.S|) (expr_18_1 Int) (expr_18_2 Int) (expr_20_1 Int) (expr_21_1 Int) (expr_24_0 |struct C.S|) (expr_25_1 Int) (expr_27_1 Int) (expr_28_1 Bool) (funds_2_0 Int) (s_13_0 |struct C.S|) (s_13_1 |struct C.S|) (s_13_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_9_function_f__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_13_0 state_1 s_13_1) (and (summary_3_function_f__32_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 s_13_1 state_3 s_13_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3718117190)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 221)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 157)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 247)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 70)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= s_13_1 s_13_0))) true))))))) true) (summary_4_function_f__32_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 s_13_0 state_3 s_13_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_16_0 |struct C.S|) (expr_16_1 |struct C.S|) (expr_16_2 |struct C.S|) (expr_16_3 |struct C.S|) (expr_18_1 Int) (expr_18_2 Int) (expr_20_1 Int) (expr_21_1 Int) (expr_24_0 |struct C.S|) (expr_25_1 Int) (expr_27_1 Int) (expr_28_1 Bool) (funds_2_0 Int) (s_13_0 |struct C.S|) (s_13_1 |struct C.S|) (s_13_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_33_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_13_0 state_1 s_13_1) (= error_0 0))) (interface_0_C_33_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_10_C_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_11_C_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_16_0 |struct C.S|) (expr_16_1 |struct C.S|) (expr_16_2 |struct C.S|) (expr_16_3 |struct C.S|) (expr_18_1 Int) (expr_18_2 Int) (expr_20_1 Int) (expr_21_1 Int) (expr_24_0 |struct C.S|) (expr_25_1 Int) (expr_27_1 Int) (expr_28_1 Bool) (funds_2_0 Int) (s_13_0 |struct C.S|) (s_13_1 |struct C.S|) (s_13_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_11_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_12_C_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_16_0 |struct C.S|) (expr_16_1 |struct C.S|) (expr_16_2 |struct C.S|) (expr_16_3 |struct C.S|) (expr_18_1 Int) (expr_18_2 Int) (expr_20_1 Int) (expr_21_1 Int) (expr_24_0 |struct C.S|) (expr_25_1 Int) (expr_27_1 Int) (expr_28_1 Bool) (funds_2_0 Int) (s_13_0 |struct C.S|) (s_13_1 |struct C.S|) (s_13_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_11_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_12_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_16_0 |struct C.S|) (expr_16_1 |struct C.S|) (expr_16_2 |struct C.S|) (expr_16_3 |struct C.S|) (expr_18_1 Int) (expr_18_2 Int) (expr_20_1 Int) (expr_21_1 Int) (expr_24_0 |struct C.S|) (expr_25_1 Int) (expr_27_1 Int) (expr_28_1 Bool) (funds_2_0 Int) (s_13_0 |struct C.S|) (s_13_1 |struct C.S|) (s_13_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_12_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_10_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_13_C_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_16_0 |struct C.S|) (expr_16_1 |struct C.S|) (expr_16_2 |struct C.S|) (expr_16_3 |struct C.S|) (expr_18_1 Int) (expr_18_2 Int) (expr_20_1 Int) (expr_21_1 Int) (expr_24_0 |struct C.S|) (expr_25_1 Int) (expr_27_1 Int) (expr_28_1 Bool) (funds_2_0 Int) (s_13_0 |struct C.S|) (s_13_1 |struct C.S|) (s_13_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_13_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_16_0 |struct C.S|) (expr_16_1 |struct C.S|) (expr_16_2 |struct C.S|) (expr_16_3 |struct C.S|) (expr_18_1 Int) (expr_18_2 Int) (expr_20_1 Int) (expr_21_1 Int) (expr_24_0 |struct C.S|) (expr_25_1 Int) (expr_27_1 Int) (expr_28_1 Bool) (funds_2_0 Int) (s_13_0 |struct C.S|) (s_13_1 |struct C.S|) (s_13_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_13_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_10_C_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_C_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_16_0 |struct C.S|) (expr_16_1 |struct C.S|) (expr_16_2 |struct C.S|) (expr_16_3 |struct C.S|) (expr_18_1 Int) (expr_18_2 Int) (expr_20_1 Int) (expr_21_1 Int) (expr_24_0 |struct C.S|) (expr_25_1 Int) (expr_27_1 Int) (expr_28_1 Bool) (funds_2_0 Int) (s_13_0 |struct C.S|) (s_13_1 |struct C.S|) (s_13_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_13_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_10_C_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_C_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_16_0 |struct C.S|) (expr_16_1 |struct C.S|) (expr_16_2 |struct C.S|) (expr_16_3 |struct C.S|) (expr_18_1 Int) (expr_18_2 Int) (expr_20_1 Int) (expr_21_1 Int) (expr_24_0 |struct C.S|) (expr_25_1 Int) (expr_27_1 Int) (expr_28_1 Bool) (funds_2_0 Int) (s_13_0 |struct C.S|) (s_13_1 |struct C.S|) (s_13_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_2_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_33_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_16_0 |struct C.S|) (expr_16_1 |struct C.S|) (expr_16_2 |struct C.S|) (expr_16_3 |struct C.S|) (expr_18_1 Int) (expr_18_2 Int) (expr_20_1 Int) (expr_21_1 Int) (expr_24_0 |struct C.S|) (expr_25_1 Int) (expr_27_1 Int) (expr_28_1 Bool) (funds_2_0 Int) (s_13_0 |struct C.S|) (s_13_1 |struct C.S|) (s_13_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_33_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_13_0 state_1 s_13_1) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_16_0 |struct C.S|) (expr_16_1 |struct C.S|) (expr_16_2 |struct C.S|) (expr_16_3 |struct C.S|) (expr_18_1 Int) (expr_18_2 Int) (expr_20_1 Int) (expr_21_1 Int) (expr_24_0 |struct C.S|) (expr_25_1 Int) (expr_27_1 Int) (expr_28_1 Bool) (funds_2_0 Int) (s_13_0 |struct C.S|) (s_13_1 |struct C.S|) (s_13_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_3_0 false)))
(check-sat)