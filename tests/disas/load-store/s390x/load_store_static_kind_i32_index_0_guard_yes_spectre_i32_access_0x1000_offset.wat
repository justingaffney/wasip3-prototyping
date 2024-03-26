;;! target = "s390x"
;;! test = "compile"
;;! flags = " -C cranelift-enable-heap-access-spectre-mitigation -O static-memory-forced -O static-memory-guard-size=0 -O dynamic-memory-guard-size=0"

;; !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
;; !!! GENERATED BY 'make-load-store-tests.sh' DO NOT EDIT !!!
;; !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

(module
  (memory i32 1)

  (func (export "do_store") (param i32 i32)
    local.get 0
    local.get 1
    i32.store offset=0x1000)

  (func (export "do_load") (param i32) (result i32)
    local.get 0
    i32.load offset=0x1000))

;; wasm[0]::function[0]:
;;    0: stmg    %r6, %r15, 0x30(%r15)
;;    6: lgr     %r1, %r15
;;    a: aghi    %r15, -0xa0
;;    e: stg     %r1, 0(%r15)
;;   14: llgfr   %r4, %r4
;;   18: lghi    %r3, 0
;;   1c: lgr     %r6, %r4
;;   20: ag      %r6, 0x50(%r2)
;;   26: aghik   %r2, %r6, 0x1000
;;   2c: clgfi   %r4, 0xffffeffc
;;   32: locgrh  %r2, %r3
;;   36: strv    %r5, 0(%r2)
;;   3c: lmg     %r6, %r15, 0xd0(%r15)
;;   42: br      %r14
;;
;; wasm[0]::function[1]:
;;   44: stmg    %r14, %r15, 0x70(%r15)
;;   4a: lgr     %r1, %r15
;;   4e: aghi    %r15, -0xa0
;;   52: stg     %r1, 0(%r15)
;;   58: llgfr   %r4, %r4
;;   5c: lghi    %r3, 0
;;   60: lgr     %r5, %r4
;;   64: ag      %r5, 0x50(%r2)
;;   6a: aghik   %r2, %r5, 0x1000
;;   70: clgfi   %r4, 0xffffeffc
;;   76: locgrh  %r2, %r3
;;   7a: lrv     %r2, 0(%r2)
;;   80: lmg     %r14, %r15, 0x110(%r15)
;;   86: br      %r14
