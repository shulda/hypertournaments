import Mathlib.Data.Fin.Basic

/-!
# Executable five-vertex ternary catalogue

The bit positions are the lexicographic triples
012,013,014,023,024,034,123,124,134,234. Each Boolean bit is the
orientation value of the corresponding increasing tuple in `Hyper`.
The semantic correctness of this finite lookup table is proved in
`CatalogueEncoding`, `CatalogueAction`, `CatalogueInvariant`,
`CatalogueRecognition`, and `CatalogueIsomorphism`; this module supplies
computable data. The semantic four-support bridge is separate.

Source: the July 2026 five-constrained classification supplement,
SHA-256 d15fbb89b7e22c1cde1402e1ce417fd74566dd10d38d145b355d6ec9cf9bbcb3.
-/

set_option maxRecDepth 32768

namespace Hypertournaments.FiveConstrained

/-- The twelve least signed-permutation orbit representatives. -/
def representative (t : Fin 12) : ℕ :=
  #[0, 1, 2, 9, 10, 11, 12, 13, 25, 41, 82, 83][t.val]!

/-- Four-vertex local-index supports, with bits 0,1,2 naming H4,O4,C4. -/
def support4 (t : Fin 12) : ℕ :=
  #[4, 6, 6, 7, 6, 6, 6, 7, 5, 7, 3, 3][t.val]!

/- The complete signed-orbit lookup, in increasing ten-bit mask order. -/
/-- A balanced ten-step lookup, so kernel reflection does not scan a 1024-entry list. -/
def type5Lookup (m : ℕ) : Fin 12 :=
  if m < 512 then
    (if m < 256 then
      (if m < 128 then
        (if m < 64 then
          (if m < 32 then
            (if m < 16 then
              (if m < 8 then
                (if m < 4 then (if m < 2 then (if m < 1 then (0) else (1)) else (if m < 3 then (2) else (1))) else (if m < 6 then (if m < 5 then (1) else (2)) else (if m < 7 then (1) else (0))))
              else
                (if m < 12 then (if m < 10 then (if m < 9 then (2) else (3)) else (if m < 11 then (4) else (5))) else (if m < 14 then (if m < 13 then (6) else (7)) else (if m < 15 then (2) else (1)))))
            else
              (if m < 24 then
                (if m < 20 then (if m < 18 then (if m < 17 then (2) else (7)) else (if m < 19 then (6) else (3))) else (if m < 22 then (if m < 21 then (1) else (6)) else (if m < 23 then (1) else (2))))
              else
                (if m < 28 then (if m < 26 then (if m < 25 then (4) else (8)) else (if m < 27 then (2) else (7))) else (if m < 30 then (if m < 29 then (2) else (3)) else (if m < 31 then (0) else (1))))))
          else
            (if m < 48 then
              (if m < 40 then
                (if m < 36 then (if m < 34 then (if m < 33 then (1) else (5)) else (if m < 35 then (3) else (7))) else (if m < 38 then (if m < 37 then (2) else (4)) else (if m < 39 then (6) else (2))))
              else
                (if m < 44 then (if m < 42 then (if m < 41 then (7) else (9)) else (if m < 43 then (8) else (9))) else (if m < 46 then (if m < 45 then (3) else (8)) else (if m < 47 then (7) else (3)))))
            else
              (if m < 56 then
                (if m < 52 then (if m < 50 then (if m < 49 then (1) else (3)) else (if m < 51 then (7) else (8))) else (if m < 54 then (if m < 53 then (0) else (2)) else (if m < 55 then (2) else (4))))
              else
                (if m < 60 then (if m < 58 then (if m < 57 then (5) else (9)) else (if m < 59 then (3) else (9))) else (if m < 62 then (if m < 61 then (1) else (7)) else (if m < 63 then (1) else (5)))))))
        else
          (if m < 96 then
            (if m < 80 then
              (if m < 72 then
                (if m < 68 then (if m < 66 then (if m < 65 then (1) else (2)) else (if m < 67 then (7) else (6))) else (if m < 70 then (if m < 69 then (5) else (4)) else (if m < 71 then (3) else (2))))
              else
                (if m < 76 then (if m < 74 then (if m < 73 then (1) else (6)) else (if m < 75 then (5) else (5))) else (if m < 78 then (if m < 77 then (5) else (5)) else (if m < 79 then (6) else (1)))))
            else
              (if m < 88 then
                (if m < 84 then (if m < 82 then (if m < 81 then (6) else (3)) else (if m < 83 then (10) else (11))) else (if m < 86 then (if m < 85 then (5) else (5)) else (if m < 87 then (7) else (6))))
              else
                (if m < 92 then (if m < 90 then (if m < 89 then (2) else (7)) else (if m < 91 then (6) else (3))) else (if m < 94 then (if m < 93 then (4) else (5)) else (if m < 95 then (2) else (1))))))
          else
            (if m < 112 then
              (if m < 104 then
                (if m < 100 then (if m < 98 then (if m < 97 then (5) else (6)) else (if m < 99 then (9) else (10))) else (if m < 102 then (if m < 101 then (6) else (2)) else (if m < 103 then (11) else (6))))
              else
                (if m < 108 then (if m < 106 then (if m < 105 then (3) else (11)) else (if m < 107 then (9) else (9))) else (if m < 110 then (if m < 109 then (7) else (3)) else (if m < 111 then (10) else (7)))))
            else
              (if m < 120 then
                (if m < 116 then (if m < 114 then (if m < 113 then (5) else (7)) else (if m < 115 then (9) else (9))) else (if m < 118 then (if m < 117 then (1) else (1)) else (if m < 119 then (3) else (5))))
              else
                (if m < 124 then (if m < 122 then (if m < 121 then (6) else (10)) else (if m < 123 then (11) else (9))) else (if m < 126 then (if m < 125 then (2) else (6)) else (if m < 127 then (6) else (5))))))))
      else
        (if m < 192 then
          (if m < 160 then
            (if m < 144 then
              (if m < 136 then
                (if m < 132 then (if m < 130 then (if m < 129 then (2) else (1)) else (if m < 131 then (6) else (1))) else (if m < 134 then (if m < 133 then (3) else (6)) else (if m < 135 then (7) else (2))))
              else
                (if m < 140 then (if m < 138 then (if m < 137 then (6) else (7)) else (if m < 139 then (5) else (5))) else (if m < 142 then (if m < 141 then (11) else (10)) else (if m < 143 then (3) else (6)))))
            else
              (if m < 152 then
                (if m < 148 then (if m < 146 then (if m < 145 then (4) else (5)) else (if m < 147 then (5) else (5))) else (if m < 150 then (if m < 149 then (5) else (5)) else (if m < 151 then (5) else (4))))
              else
                (if m < 156 then (if m < 154 then (if m < 153 then (2) else (3)) else (if m < 155 then (1) else (6))) else (if m < 158 then (if m < 157 then (6) else (7)) else (if m < 159 then (1) else (2))))))
          else
            (if m < 176 then
              (if m < 168 then
                (if m < 164 then (if m < 162 then (if m < 161 then (6) else (5)) else (if m < 163 then (11) else (3))) else (if m < 166 then (if m < 165 then (7) else (5)) else (if m < 167 then (10) else (6))))
              else
                (if m < 172 then (if m < 170 then (if m < 169 then (10) else (9)) else (if m < 171 then (9) else (9))) else (if m < 174 then (if m < 173 then (9) else (9)) else (if m < 175 then (9) else (11)))))
            else
              (if m < 184 then
                (if m < 180 then (if m < 178 then (if m < 177 then (2) else (6)) else (if m < 179 then (3) else (7))) else (if m < 182 then (if m < 181 then (1) else (1)) else (if m < 183 then (6) else (2))))
              else
                (if m < 188 then (if m < 186 then (if m < 185 then (6) else (11)) else (if m < 187 then (7) else (10))) else (if m < 190 then (if m < 189 then (5) else (3)) else (if m < 191 then (5) else (6)))))))
        else
          (if m < 224 then
            (if m < 208 then
              (if m < 200 then
                (if m < 196 then (if m < 194 then (if m < 193 then (1) else (0)) else (if m < 195 then (3) else (2))) else (if m < 198 then (if m < 197 then (7) else (2)) else (if m < 199 then (8) else (4))))
              else
                (if m < 204 then (if m < 202 then (if m < 201 then (1) else (2)) else (if m < 203 then (5) else (4))) else (if m < 206 then (if m < 205 then (3) else (6)) else (if m < 207 then (7) else (2)))))
            else
              (if m < 216 then
                (if m < 212 then (if m < 210 then (if m < 209 then (2) else (1)) else (if m < 211 then (7) else (6))) else (if m < 214 then (if m < 213 then (6) else (1)) else (if m < 215 then (3) else (2))))
              else
                (if m < 220 then (if m < 218 then (if m < 217 then (0) else (1)) else (if m < 219 then (1) else (2))) else (if m < 222 then (if m < 221 then (2) else (1)) else (if m < 223 then (1) else (0))))))
          else
            (if m < 240 then
              (if m < 232 then
                (if m < 228 then (if m < 226 then (if m < 225 then (5) else (1)) else (if m < 227 then (9) else (7))) else (if m < 230 then (if m < 229 then (3) else (1)) else (if m < 231 then (9) else (5))))
              else
                (if m < 236 then (if m < 234 then (if m < 233 then (7) else (3)) else (if m < 235 then (9) else (8))) else (if m < 238 then (if m < 237 then (8) else (7)) else (if m < 239 then (9) else (3)))))
            else
              (if m < 248 then
                (if m < 244 then (if m < 242 then (if m < 241 then (4) else (2)) else (if m < 243 then (8) else (3))) else (if m < 246 then (if m < 245 then (2) else (0)) else (if m < 247 then (7) else (1))))
              else
                (if m < 252 then (if m < 250 then (if m < 249 then (2) else (6)) else (if m < 251 then (3) else (7))) else (if m < 254 then (if m < 253 then (4) else (2)) else (if m < 255 then (5) else (1)))))))))
    else
      (if m < 384 then
        (if m < 320 then
          (if m < 288 then
            (if m < 272 then
              (if m < 264 then
                (if m < 260 then (if m < 258 then (if m < 257 then (2) else (6)) else (if m < 259 then (4) else (2))) else (if m < 262 then (if m < 261 then (7) else (3)) else (if m < 263 then (5) else (1))))
              else
                (if m < 268 then (if m < 266 then (if m < 265 then (6) else (11)) else (if m < 267 then (2) else (6))) else (if m < 270 then (if m < 269 then (10) else (9)) else (if m < 271 then (6) else (5)))))
            else
              (if m < 280 then
                (if m < 276 then (if m < 274 then (if m < 273 then (6) else (10)) else (if m < 275 then (5) else (7))) else (if m < 278 then (if m < 277 then (3) else (11)) else (if m < 279 then (5) else (6))))
              else
                (if m < 284 then (if m < 282 then (if m < 281 then (5) else (9)) else (if m < 283 then (1) else (3))) else (if m < 286 then (if m < 285 then (7) else (9)) else (if m < 287 then (1) else (5))))))
          else
            (if m < 304 then
              (if m < 296 then
                (if m < 292 then (if m < 290 then (if m < 289 then (1) else (5)) else (if m < 291 then (5) else (6))) else (if m < 294 then (if m < 293 then (6) else (5)) else (if m < 295 then (5) else (1))))
              else
                (if m < 300 then (if m < 298 then (if m < 297 then (3) else (9)) else (if m < 299 then (7) else (10))) else (if m < 302 then (if m < 301 then (11) else (9)) else (if m < 303 then (3) else (7)))))
            else
              (if m < 312 then
                (if m < 308 then (if m < 306 then (if m < 305 then (1) else (7)) else (if m < 307 then (5) else (3))) else (if m < 310 then (if m < 309 then (2) else (6)) else (if m < 311 then (4) else (2))))
              else
                (if m < 316 then (if m < 314 then (if m < 313 then (5) else (9)) else (if m < 315 then (6) else (11))) else (if m < 318 then (if m < 317 then (6) else (10)) else (if m < 319 then (2) else (6)))))))
        else
          (if m < 352 then
            (if m < 336 then
              (if m < 328 then
                (if m < 324 then (if m < 322 then (if m < 321 then (3) else (7)) else (if m < 323 then (8) else (3))) else (if m < 326 then (if m < 325 then (9) else (8)) else (if m < 327 then (9) else (7))))
              else
                (if m < 332 then (if m < 330 then (if m < 329 then (7) else (10)) else (if m < 331 then (3) else (7))) else (if m < 334 then (if m < 333 then (9) else (9)) else (if m < 335 then (11) else (3)))))
            else
              (if m < 344 then
                (if m < 340 then (if m < 338 then (if m < 337 then (11) else (9)) else (if m < 339 then (9) else (9))) else (if m < 342 then (if m < 341 then (9) else (9)) else (if m < 343 then (9) else (10))))
              else
                (if m < 348 then (if m < 346 then (if m < 345 then (3) else (9)) else (if m < 347 then (7) else (8))) else (if m < 350 then (if m < 349 then (8) else (9)) else (if m < 351 then (3) else (7))))))
          else
            (if m < 368 then
              (if m < 360 then
                (if m < 356 then (if m < 354 then (if m < 353 then (7) else (3)) else (if m < 355 then (9) else (11))) else (if m < 358 then (if m < 357 then (10) else (7)) else (if m < 359 then (9) else (3))))
              else
                (if m < 364 then (if m < 362 then (if m < 361 then (8) else (9)) else (if m < 363 then (9) else (9))) else (if m < 366 then (if m < 365 then (9) else (9)) else (if m < 367 then (9) else (8)))))
            else
              (if m < 376 then
                (if m < 372 then (if m < 370 then (if m < 369 then (3) else (8)) else (if m < 371 then (9) else (9))) else (if m < 374 then (if m < 373 then (7) else (3)) else (if m < 375 then (8) else (7))))
              else
                (if m < 380 then (if m < 378 then (if m < 377 then (7) else (9)) else (if m < 379 then (10) else (9))) else (if m < 382 then (if m < 381 then (3) else (11)) else (if m < 383 then (7) else (3))))))))
      else
        (if m < 448 then
          (if m < 416 then
            (if m < 400 then
              (if m < 392 then
                (if m < 388 then (if m < 386 then (if m < 385 then (4) else (2)) else (if m < 387 then (2) else (0))) else (if m < 390 then (if m < 389 then (8) else (7)) else (if m < 391 then (3) else (1))))
              else
                (if m < 396 then (if m < 394 then (if m < 393 then (5) else (3)) else (if m < 395 then (1) else (1))) else (if m < 398 then (if m < 397 then (9) else (9)) else (if m < 399 then (7) else (5)))))
            else
              (if m < 408 then
                (if m < 404 then (if m < 402 then (if m < 401 then (2) else (6)) else (if m < 403 then (1) else (1))) else (if m < 406 then (if m < 405 then (7) else (3)) else (if m < 407 then (6) else (2))))
              else
                (if m < 412 then (if m < 410 then (if m < 409 then (1) else (7)) else (if m < 411 then (0) else (2))) else (if m < 414 then (if m < 413 then (3) else (8)) else (if m < 415 then (2) else (4))))))
          else
            (if m < 432 then
              (if m < 424 then
                (if m < 420 then (if m < 418 then (if m < 417 then (2) else (4)) else (if m < 419 then (6) else (2))) else (if m < 422 then (if m < 421 then (3) else (5)) else (if m < 423 then (7) else (1))))
              else
                (if m < 428 then (if m < 426 then (if m < 425 then (7) else (8)) else (if m < 427 then (3) else (7))) else (if m < 430 then (if m < 429 then (9) else (9)) else (if m < 431 then (8) else (3)))))
            else
              (if m < 440 then
                (if m < 436 then (if m < 434 then (if m < 433 then (0) else (2)) else (if m < 435 then (1) else (1))) else (if m < 438 then (if m < 437 then (1) else (1)) else (if m < 439 then (2) else (0))))
              else
                (if m < 444 then (if m < 442 then (if m < 441 then (1) else (3)) else (if m < 443 then (2) else (6))) else (if m < 446 then (if m < 445 then (5) else (7)) else (if m < 447 then (4) else (2)))))))
        else
          (if m < 480 then
            (if m < 464 then
              (if m < 456 then
                (if m < 452 then (if m < 450 then (if m < 449 then (5) else (1)) else (if m < 451 then (7) else (1))) else (if m < 454 then (if m < 453 then (9) else (3)) else (if m < 455 then (9) else (5))))
              else
                (if m < 460 then (if m < 458 then (if m < 457 then (5) else (6)) else (if m < 459 then (6) else (2))) else (if m < 462 then (if m < 461 then (9) else (11)) else (if m < 463 then (10) else (6)))))
            else
              (if m < 472 then
                (if m < 468 then (if m < 466 then (if m < 465 then (6) else (5)) else (if m < 467 then (3) else (5))) else (if m < 470 then (if m < 469 then (10) else (7)) else (if m < 471 then (11) else (6))))
              else
                (if m < 476 then (if m < 474 then (if m < 473 then (1) else (5)) else (if m < 475 then (2) else (4))) else (if m < 478 then (if m < 477 then (7) else (3)) else (if m < 479 then (6) else (2))))))
          else
            (if m < 496 then
              (if m < 488 then
                (if m < 484 then (if m < 482 then (if m < 481 then (6) else (2)) else (if m < 483 then (10) else (6))) else (if m < 486 then (if m < 485 then (11) else (6)) else (if m < 487 then (9) else (5))))
              else
                (if m < 492 then (if m < 490 then (if m < 489 then (3) else (7)) else (if m < 491 then (11) else (3))) else (if m < 494 then (if m < 493 then (9) else (10)) else (if m < 495 then (9) else (7)))))
            else
              (if m < 504 then
                (if m < 500 then (if m < 498 then (if m < 497 then (2) else (4)) else (if m < 499 then (7) else (5))) else (if m < 502 then (if m < 501 then (6) else (2)) else (if m < 503 then (3) else (1))))
              else
                (if m < 508 then (if m < 506 then (if m < 505 then (1) else (5)) else (if m < 507 then (6) else (5))) else (if m < 510 then (if m < 509 then (5) else (6)) else (if m < 511 then (5) else (1))))))))))
  else
    (if m < 768 then
      (if m < 640 then
        (if m < 576 then
          (if m < 544 then
            (if m < 528 then
              (if m < 520 then
                (if m < 516 then (if m < 514 then (if m < 513 then (1) else (5)) else (if m < 515 then (6) else (5))) else (if m < 518 then (if m < 517 then (5) else (6)) else (if m < 519 then (5) else (1))))
              else
                (if m < 524 then (if m < 522 then (if m < 521 then (1) else (7)) else (if m < 523 then (2) else (6))) else (if m < 526 then (if m < 525 then (5) else (3)) else (if m < 527 then (4) else (2)))))
            else
              (if m < 536 then
                (if m < 532 then (if m < 530 then (if m < 529 then (3) else (9)) else (if m < 531 then (11) else (9))) else (if m < 534 then (if m < 533 then (7) else (10)) else (if m < 535 then (3) else (7))))
              else
                (if m < 540 then (if m < 538 then (if m < 537 then (5) else (9)) else (if m < 539 then (6) else (10))) else (if m < 542 then (if m < 541 then (6) else (11)) else (if m < 543 then (2) else (6))))))
          else
            (if m < 560 then
              (if m < 552 then
                (if m < 548 then (if m < 546 then (if m < 545 then (2) else (6)) else (if m < 547 then (7) else (3))) else (if m < 550 then (if m < 549 then (4) else (2)) else (if m < 551 then (5) else (1))))
              else
                (if m < 556 then (if m < 554 then (if m < 553 then (6) else (10)) else (if m < 555 then (3) else (11))) else (if m < 558 then (if m < 557 then (5) else (7)) else (if m < 559 then (5) else (6)))))
            else
              (if m < 568 then
                (if m < 564 then (if m < 562 then (if m < 561 then (6) else (11)) else (if m < 563 then (10) else (9))) else (if m < 566 then (if m < 565 then (2) else (6)) else (if m < 567 then (6) else (5))))
              else
                (if m < 572 then (if m < 570 then (if m < 569 then (5) else (9)) else (if m < 571 then (7) else (9))) else (if m < 574 then (if m < 573 then (1) else (3)) else (if m < 575 then (1) else (5)))))))
        else
          (if m < 608 then
            (if m < 592 then
              (if m < 584 then
                (if m < 580 then (if m < 578 then (if m < 577 then (2) else (4)) else (if m < 579 then (3) else (5))) else (if m < 582 then (if m < 581 then (6) else (2)) else (if m < 583 then (7) else (1))))
              else
                (if m < 588 then (if m < 586 then (if m < 585 then (0) else (2)) else (if m < 587 then (1) else (1))) else (if m < 590 then (if m < 589 then (1) else (1)) else (if m < 591 then (2) else (0)))))
            else
              (if m < 600 then
                (if m < 596 then (if m < 594 then (if m < 593 then (7) else (8)) else (if m < 595 then (9) else (9))) else (if m < 598 then (if m < 597 then (3) else (7)) else (if m < 599 then (8) else (3))))
              else
                (if m < 604 then (if m < 602 then (if m < 601 then (1) else (3)) else (if m < 603 then (5) else (7))) else (if m < 606 then (if m < 605 then (2) else (6)) else (if m < 607 then (4) else (2))))))
          else
            (if m < 624 then
              (if m < 616 then
                (if m < 612 then (if m < 610 then (if m < 609 then (4) else (2)) else (if m < 611 then (8) else (7))) else (if m < 614 then (if m < 613 then (2) else (0)) else (if m < 615 then (3) else (1))))
              else
                (if m < 620 then (if m < 618 then (if m < 617 then (2) else (6)) else (if m < 619 then (7) else (3))) else (if m < 622 then (if m < 621 then (1) else (1)) else (if m < 623 then (6) else (2)))))
            else
              (if m < 632 then
                (if m < 628 then (if m < 626 then (if m < 625 then (5) else (3)) else (if m < 627 then (9) else (9))) else (if m < 630 then (if m < 629 then (1) else (1)) else (if m < 631 then (7) else (5))))
              else
                (if m < 636 then (if m < 634 then (if m < 633 then (1) else (7)) else (if m < 635 then (3) else (8))) else (if m < 638 then (if m < 637 then (0) else (2)) else (if m < 639 then (2) else (4))))))))
      else
        (if m < 704 then
          (if m < 672 then
            (if m < 656 then
              (if m < 648 then
                (if m < 644 then (if m < 642 then (if m < 641 then (7) else (3)) else (if m < 643 then (10) else (7))) else (if m < 646 then (if m < 645 then (9) else (11)) else (if m < 647 then (9) else (3))))
              else
                (if m < 652 then (if m < 650 then (if m < 649 then (3) else (8)) else (if m < 651 then (7) else (3))) else (if m < 654 then (if m < 653 then (9) else (9)) else (if m < 655 then (8) else (7)))))
            else
              (if m < 664 then
                (if m < 660 then (if m < 658 then (if m < 657 then (8) else (9)) else (if m < 659 then (9) else (9))) else (if m < 662 then (if m < 661 then (9) else (9)) else (if m < 663 then (9) else (8))))
              else
                (if m < 668 then (if m < 666 then (if m < 665 then (7) else (9)) else (if m < 667 then (3) else (11))) else (if m < 670 then (if m < 669 then (10) else (9)) else (if m < 671 then (7) else (3))))))
          else
            (if m < 688 then
              (if m < 680 then
                (if m < 676 then (if m < 674 then (if m < 673 then (3) else (7)) else (if m < 675 then (9) else (8))) else (if m < 678 then (if m < 677 then (8) else (3)) else (if m < 679 then (9) else (7))))
              else
                (if m < 684 then (if m < 682 then (if m < 681 then (11) else (9)) else (if m < 683 then (9) else (9))) else (if m < 686 then (if m < 685 then (9) else (9)) else (if m < 687 then (9) else (10)))))
            else
              (if m < 696 then
                (if m < 692 then (if m < 690 then (if m < 689 then (7) else (10)) else (if m < 691 then (9) else (9))) else (if m < 694 then (if m < 693 then (3) else (7)) else (if m < 695 then (11) else (3))))
              else
                (if m < 700 then (if m < 698 then (if m < 697 then (3) else (9)) else (if m < 699 then (8) else (9))) else (if m < 702 then (if m < 701 then (7) else (8)) else (if m < 703 then (3) else (7)))))))
        else
          (if m < 736 then
            (if m < 720 then
              (if m < 712 then
                (if m < 708 then (if m < 706 then (if m < 705 then (6) else (2)) else (if m < 707 then (11) else (6))) else (if m < 710 then (if m < 709 then (10) else (6)) else (if m < 711 then (9) else (5))))
              else
                (if m < 716 then (if m < 714 then (if m < 713 then (2) else (4)) else (if m < 715 then (6) else (2))) else (if m < 718 then (if m < 717 then (7) else (5)) else (if m < 719 then (3) else (1)))))
            else
              (if m < 728 then
                (if m < 724 then (if m < 722 then (if m < 721 then (3) else (7)) else (if m < 723 then (9) else (10))) else (if m < 726 then (if m < 725 then (11) else (3)) else (if m < 727 then (9) else (7))))
              else
                (if m < 732 then (if m < 730 then (if m < 729 then (1) else (5)) else (if m < 731 then (5) else (6))) else (if m < 734 then (if m < 733 then (6) else (5)) else (if m < 735 then (5) else (1))))))
          else
            (if m < 752 then
              (if m < 744 then
                (if m < 740 then (if m < 738 then (if m < 737 then (5) else (1)) else (if m < 739 then (9) else (3))) else (if m < 742 then (if m < 741 then (7) else (1)) else (if m < 743 then (9) else (5))))
              else
                (if m < 748 then (if m < 746 then (if m < 745 then (6) else (5)) else (if m < 747 then (10) else (7))) else (if m < 750 then (if m < 749 then (3) else (5)) else (if m < 751 then (11) else (6)))))
            else
              (if m < 760 then
                (if m < 756 then (if m < 754 then (if m < 753 then (5) else (6)) else (if m < 755 then (9) else (11))) else (if m < 758 then (if m < 757 then (6) else (2)) else (if m < 759 then (10) else (6))))
              else
                (if m < 764 then (if m < 762 then (if m < 761 then (1) else (5)) else (if m < 763 then (7) else (3))) else (if m < 766 then (if m < 765 then (2) else (4)) else (if m < 767 then (6) else (2)))))))))
    else
      (if m < 896 then
        (if m < 832 then
          (if m < 800 then
            (if m < 784 then
              (if m < 776 then
                (if m < 772 then (if m < 770 then (if m < 769 then (1) else (5)) else (if m < 771 then (2) else (4))) else (if m < 774 then (if m < 773 then (3) else (7)) else (if m < 775 then (6) else (2))))
              else
                (if m < 780 then (if m < 778 then (if m < 777 then (1) else (3)) else (if m < 779 then (0) else (2))) else (if m < 782 then (if m < 781 then (7) else (8)) else (if m < 783 then (2) else (4)))))
            else
              (if m < 792 then
                (if m < 788 then (if m < 786 then (if m < 785 then (7) else (9)) else (if m < 787 then (3) else (8))) else (if m < 790 then (if m < 789 then (8) else (9)) else (if m < 791 then (7) else (3))))
              else
                (if m < 796 then (if m < 794 then (if m < 793 then (5) else (9)) else (if m < 795 then (1) else (7))) else (if m < 798 then (if m < 797 then (3) else (9)) else (if m < 799 then (1) else (5))))))
          else
            (if m < 816 then
              (if m < 808 then
                (if m < 804 then (if m < 802 then (if m < 801 then (0) else (1)) else (if m < 803 then (1) else (2))) else (if m < 806 then (if m < 805 then (2) else (1)) else (if m < 807 then (1) else (0))))
              else
                (if m < 812 then (if m < 810 then (if m < 809 then (2) else (7)) else (if m < 811 then (1) else (6))) else (if m < 814 then (if m < 813 then (6) else (3)) else (if m < 815 then (1) else (2)))))
            else
              (if m < 824 then
                (if m < 820 then (if m < 818 then (if m < 817 then (2) else (3)) else (if m < 819 then (6) else (7))) else (if m < 822 then (if m < 821 then (4) else (5)) else (if m < 823 then (2) else (1))))
              else
                (if m < 828 then (if m < 826 then (if m < 825 then (4) else (8)) else (if m < 827 then (2) else (3))) else (if m < 830 then (if m < 829 then (2) else (7)) else (if m < 831 then (0) else (1)))))))
        else
          (if m < 864 then
            (if m < 848 then
              (if m < 840 then
                (if m < 836 then (if m < 834 then (if m < 833 then (6) else (5)) else (if m < 835 then (7) else (5))) else (if m < 838 then (if m < 837 then (11) else (3)) else (if m < 839 then (10) else (6))))
              else
                (if m < 844 then (if m < 842 then (if m < 841 then (2) else (6)) else (if m < 843 then (1) else (1))) else (if m < 846 then (if m < 845 then (3) else (7)) else (if m < 847 then (6) else (2)))))
            else
              (if m < 856 then
                (if m < 852 then (if m < 850 then (if m < 849 then (10) else (9)) else (if m < 851 then (9) else (9))) else (if m < 854 then (if m < 853 then (9) else (9)) else (if m < 855 then (9) else (11))))
              else
                (if m < 860 then (if m < 858 then (if m < 857 then (6) else (11)) else (if m < 859 then (5) else (3))) else (if m < 862 then (if m < 861 then (7) else (10)) else (if m < 863 then (5) else (6))))))
          else
            (if m < 880 then
              (if m < 872 then
                (if m < 868 then (if m < 866 then (if m < 865 then (2) else (1)) else (if m < 867 then (3) else (6))) else (if m < 870 then (if m < 869 then (6) else (1)) else (if m < 871 then (7) else (2))))
              else
                (if m < 876 then (if m < 874 then (if m < 873 then (4) else (5)) else (if m < 875 then (5) else (5))) else (if m < 878 then (if m < 877 then (5) else (5)) else (if m < 879 then (5) else (4)))))
            else
              (if m < 888 then
                (if m < 884 then (if m < 882 then (if m < 881 then (6) else (7)) else (if m < 883 then (11) else (10))) else (if m < 886 then (if m < 885 then (5) else (5)) else (if m < 887 then (3) else (6))))
              else
                (if m < 892 then (if m < 890 then (if m < 889 then (2) else (3)) else (if m < 891 then (6) else (7))) else (if m < 894 then (if m < 893 then (1) else (6)) else (if m < 895 then (1) else (2))))))))
      else
        (if m < 960 then
          (if m < 928 then
            (if m < 912 then
              (if m < 904 then
                (if m < 900 then (if m < 898 then (if m < 897 then (5) else (6)) else (if m < 899 then (6) else (2))) else (if m < 902 then (if m < 901 then (9) else (10)) else (if m < 903 then (11) else (6))))
              else
                (if m < 908 then (if m < 906 then (if m < 905 then (5) else (7)) else (if m < 907 then (1) else (1))) else (if m < 910 then (if m < 909 then (9) else (9)) else (if m < 911 then (3) else (5)))))
            else
              (if m < 920 then
                (if m < 916 then (if m < 914 then (if m < 913 then (3) else (11)) else (if m < 915 then (7) else (3))) else (if m < 918 then (if m < 917 then (9) else (9)) else (if m < 919 then (10) else (7))))
              else
                (if m < 924 then (if m < 922 then (if m < 921 then (6) else (10)) else (if m < 923 then (2) else (6))) else (if m < 926 then (if m < 925 then (11) else (9)) else (if m < 927 then (6) else (5))))))
          else
            (if m < 944 then
              (if m < 936 then
                (if m < 932 then (if m < 930 then (if m < 929 then (1) else (2)) else (if m < 931 then (5) else (4))) else (if m < 934 then (if m < 933 then (7) else (6)) else (if m < 935 then (3) else (2))))
              else
                (if m < 940 then (if m < 938 then (if m < 937 then (6) else (3)) else (if m < 939 then (5) else (5))) else (if m < 942 then (if m < 941 then (10) else (11)) else (if m < 943 then (7) else (6)))))
            else
              (if m < 952 then
                (if m < 948 then (if m < 946 then (if m < 945 then (1) else (6)) else (if m < 947 then (5) else (5))) else (if m < 950 then (if m < 949 then (5) else (5)) else (if m < 951 then (6) else (1))))
              else
                (if m < 956 then (if m < 954 then (if m < 953 then (2) else (7)) else (if m < 955 then (4) else (5))) else (if m < 958 then (if m < 957 then (6) else (3)) else (if m < 959 then (2) else (1)))))))
        else
          (if m < 992 then
            (if m < 976 then
              (if m < 968 then
                (if m < 964 then (if m < 962 then (if m < 961 then (5) else (1)) else (if m < 963 then (3) else (1))) else (if m < 966 then (if m < 965 then (9) else (7)) else (if m < 967 then (9) else (5))))
              else
                (if m < 972 then (if m < 970 then (if m < 969 then (4) else (2)) else (if m < 971 then (2) else (0))) else (if m < 974 then (if m < 973 then (8) else (3)) else (if m < 975 then (7) else (1)))))
            else
              (if m < 984 then
                (if m < 980 then (if m < 978 then (if m < 977 then (7) else (3)) else (if m < 979 then (8) else (7))) else (if m < 982 then (if m < 981 then (9) else (8)) else (if m < 983 then (9) else (3))))
              else
                (if m < 988 then (if m < 986 then (if m < 985 then (2) else (6)) else (if m < 987 then (4) else (2))) else (if m < 990 then (if m < 989 then (3) else (7)) else (if m < 991 then (5) else (1))))))
          else
            (if m < 1008 then
              (if m < 1000 then
                (if m < 996 then (if m < 994 then (if m < 993 then (1) else (0)) else (if m < 995 then (7) else (2))) else (if m < 998 then (if m < 997 then (3) else (2)) else (if m < 999 then (8) else (4))))
              else
                (if m < 1004 then (if m < 1002 then (if m < 1001 then (2) else (1)) else (if m < 1003 then (6) else (1))) else (if m < 1006 then (if m < 1005 then (7) else (6)) else (if m < 1007 then (3) else (2)))))
            else
              (if m < 1016 then
                (if m < 1012 then (if m < 1010 then (if m < 1009 then (1) else (2)) else (if m < 1011 then (3) else (6))) else (if m < 1014 then (if m < 1013 then (5) else (4)) else (if m < 1015 then (7) else (2))))
              else
                (if m < 1020 then (if m < 1018 then (if m < 1017 then (0) else (1)) else (if m < 1019 then (2) else (1))) else (if m < 1022 then (if m < 1021 then (1) else (2)) else (if m < 1023 then (1) else (0))))))))))

/-- Isomorphism label of a raw ten-bit orientation mask. Higher bits are ignored. -/
def type5 (mask : ℕ) : Fin 12 :=
  type5Lookup (mask % 1024)

@[simp] theorem type5_mod (mask : ℕ) : type5 (mask % 1024) = type5 mask := by
  simp [type5]

/-- Every named representative has its advertised label. -/
theorem type5_representative : ∀ t : Fin 12, type5 (representative t) = t := by
  decide

/-- Exactly the finite list advertised by the source is used. -/
theorem representative_injective : Function.Injective representative := by
  intro a b h
  have := congrArg type5 h
  simpa only [type5_representative] using this

end Hypertournaments.FiveConstrained
