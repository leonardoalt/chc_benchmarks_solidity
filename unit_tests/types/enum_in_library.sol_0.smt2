(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_L_4_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_L_4_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_L_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_L_4_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |interface_3_C_27_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_4_C_27_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_5_C_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_4_C_27_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_6_function_f__26_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_7_function_f__26_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_4_C_27_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_7_function_f__26_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 _d_10_0 state_2 _d_10_1))) (nondet_interface_4_C_27_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |contract_initializer_8_L_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_9_L_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_9_L_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_10_L_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_9_L_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_10_L_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_10_L_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_8_L_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_11_L_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_11_L_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_11_L_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_8_L_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_L_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_11_L_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_8_L_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_L_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_2_L_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_L_4_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_12_function_f__26_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_13_f_25_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (_d_10_2 Int) (_d_10_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_12_function_f__26_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _d_10_0 state_1 _d_10_1)))


(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (_d_10_2 Int) (_d_10_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12_function_f__26_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _d_10_0 state_1 _d_10_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= _d_10_1 _d_10_0))) true)) true) (block_13_f_25_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _d_10_0 state_1 _d_10_1))))


(declare-fun |block_14_return_function_f__26_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_15_function_f__26_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (_d_10_2 Int) (_d_10_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_19_0 Int) (expr_21_1 Int) (expr_22_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_13_f_25_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _d_10_0 state_1 _d_10_1) (and (= expr_22_1 (= expr_19_0 expr_21_1)) (and (=> true (and (>= expr_21_1 0) (<= expr_21_1 1))) (and (= expr_21_1 0) (and (=> true (and (>= expr_19_0 0) (<= expr_19_0 1))) (and (= expr_19_0 _d_10_2) (and (= _d_10_2 expr_16_1) (and (=> true (and (>= expr_16_1 0) (<= expr_16_1 1))) (and (= expr_16_1 expr_15_1) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 1))) (and (= expr_13_0 _d_10_1) (and (=> true (and (>= expr_15_1 0) (<= expr_15_1 1))) (and (= expr_15_1 0) (and (and (>= _d_10_1 0) (<= _d_10_1 1)) true)))))))))))))) (and (not expr_22_1) (= error_1 1))) (block_15_function_f__26_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _d_10_0 state_1 _d_10_2))))


(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (_d_10_2 Int) (_d_10_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_19_0 Int) (expr_21_1 Int) (expr_22_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_15_function_f__26_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _d_10_0 state_1 _d_10_2) (summary_6_function_f__26_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _d_10_0 state_1 _d_10_2))))


(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (_d_10_2 Int) (_d_10_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_19_0 Int) (expr_21_1 Int) (expr_22_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_13_f_25_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _d_10_0 state_1 _d_10_1) (and (= error_1 error_0) (and (= expr_22_1 (= expr_19_0 expr_21_1)) (and (=> true (and (>= expr_21_1 0) (<= expr_21_1 1))) (and (= expr_21_1 0) (and (=> true (and (>= expr_19_0 0) (<= expr_19_0 1))) (and (= expr_19_0 _d_10_2) (and (= _d_10_2 expr_16_1) (and (=> true (and (>= expr_16_1 0) (<= expr_16_1 1))) (and (= expr_16_1 expr_15_1) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 1))) (and (= expr_13_0 _d_10_1) (and (=> true (and (>= expr_15_1 0) (<= expr_15_1 1))) (and (= expr_15_1 0) (and (and (>= _d_10_1 0) (<= _d_10_1 1)) true))))))))))))))) true) (block_14_return_function_f__26_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _d_10_0 state_1 _d_10_2))))


(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (_d_10_2 Int) (_d_10_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_19_0 Int) (expr_21_1 Int) (expr_22_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_14_return_function_f__26_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _d_10_0 state_1 _d_10_1) true) true) (summary_6_function_f__26_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _d_10_0 state_1 _d_10_1))))


(declare-fun |block_16_function_f__26_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (_d_10_2 Int) (_d_10_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_19_0 Int) (expr_21_1 Int) (expr_22_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_16_function_f__26_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _d_10_0 state_1 _d_10_1)))


(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (_d_10_2 Int) (_d_10_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_19_0 Int) (expr_21_1 Int) (expr_22_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_16_function_f__26_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _d_10_0 state_1 _d_10_1) (and (summary_6_function_f__26_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 _d_10_1 state_3 _d_10_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 824235060)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 49)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 32)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 212)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 52)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= _d_10_1 _d_10_0))) true))))))) true) (summary_7_function_f__26_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _d_10_0 state_3 _d_10_2))))


(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (_d_10_2 Int) (_d_10_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_19_0 Int) (expr_21_1 Int) (expr_22_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_3_C_27_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_7_function_f__26_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _d_10_0 state_1 _d_10_1) (= error_0 0))) (interface_3_C_27_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_17_C_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_18_C_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (_d_10_2 Int) (_d_10_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_19_0 Int) (expr_21_1 Int) (expr_22_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_18_C_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_19_C_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (_d_10_2 Int) (_d_10_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_19_0 Int) (expr_21_1 Int) (expr_22_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_18_C_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_19_C_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (_d_10_2 Int) (_d_10_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_19_0 Int) (expr_21_1 Int) (expr_22_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_19_C_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_17_C_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_20_C_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (_d_10_2 Int) (_d_10_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_19_0 Int) (expr_21_1 Int) (expr_22_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_20_C_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (_d_10_2 Int) (_d_10_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_19_0 Int) (expr_21_1 Int) (expr_22_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_20_C_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_17_C_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_5_C_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (_d_10_2 Int) (_d_10_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_19_0 Int) (expr_21_1 Int) (expr_22_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_20_C_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_17_C_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_5_C_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (_d_10_2 Int) (_d_10_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_19_0 Int) (expr_21_1 Int) (expr_22_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_5_C_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_3_C_27_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (_d_10_2 Int) (_d_10_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_19_0 Int) (expr_21_1 Int) (expr_22_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_3_C_27_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_7_function_f__26_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _d_10_0 state_1 _d_10_1) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (_d_10_0 Int) (_d_10_1 Int) (_d_10_2 Int) (_d_10_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_15_1 Int) (expr_16_1 Int) (expr_19_0 Int) (expr_21_1 Int) (expr_22_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_3_0 false)))
(check-sat)