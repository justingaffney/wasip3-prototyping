;;! target = "aarch64"
;;! test = "compile"
;;! flags = " -C cranelift-enable-heap-access-spectre-mitigation -W memory64 -O static-memory-maximum-size=0 -O static-memory-guard-size=4294967295 -O dynamic-memory-guard-size=4294967295"

;; !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
;; !!! GENERATED BY 'make-load-store-tests.sh' DO NOT EDIT !!!
;; !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

(module
  (memory i64 1)

  (func (export "do_store") (param i64 i32)
    local.get 0
    local.get 1
    i32.store8 offset=0)

  (func (export "do_load") (param i64) (result i32)
    local.get 0
    i32.load8_u offset=0))

;; wasm[0]::function[0]:
;;    0: stp     x29, x30, [sp, #-0x10]!
;;    4: mov     x29, sp
;;    8: ldr     x9, [x0, #0x58]
;;    c: ldr     x11, [x0, #0x50]
;;   10: mov     x10, #0
;;   14: add     x11, x11, x2
;;   18: cmp     x2, x9
;;   1c: csel    x10, x10, x11, hs
;;   20: csdb
;;   24: strb    w3, [x10]
;;   28: ldp     x29, x30, [sp], #0x10
;;   2c: ret
;;
;; wasm[0]::function[1]:
;;   40: stp     x29, x30, [sp, #-0x10]!
;;   44: mov     x29, sp
;;   48: ldr     x9, [x0, #0x58]
;;   4c: ldr     x11, [x0, #0x50]
;;   50: mov     x10, #0
;;   54: add     x11, x11, x2
;;   58: cmp     x2, x9
;;   5c: csel    x10, x10, x11, hs
;;   60: csdb
;;   64: ldrb    w0, [x10]
;;   68: ldp     x29, x30, [sp], #0x10
;;   6c: ret
