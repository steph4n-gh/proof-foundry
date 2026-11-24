import PnP.Core
import PnP.Statements.L_rec_php4

/-!
  L-rec-php4 lower bound at score 84: `¬ PnP.Statements.L_rec_php4.Record 84`,
  proving that every tree-like resolution refutation of `PHP(4, 3)` has at least 85 nodes
  (43 leaves), closing `L-rec-php4` to exact optimality (matching the 85-node refutation
  in `L_rec_php4_s85`).
-/

namespace PnP.Lemmas.L_rec_php4_not_s84

open PnP

/-! ## 1. Balanced BST of exact leaf lower bounds for all 814 canonical orbits -/

private inductive BST where
  | leaf
  | n (k v : Nat) (l r : BST)

private def BST.find : BST → Nat → Nat
  | .leaf, _ => 0
  | .n k v l r, x =>
    if x == k then v
    else if x < k then l.find x
    else r.find x

private def dpBST : BST :=
  (.n 21988 5 (.n 3063 2 (.n 849 8 (.n 159 4 (.n 58 8 (.n 31 10 (.n 14 14 (.n 4 15 (.n 1 29 (.n 0 43 .leaf .leaf) (.n 2 14 .leaf .leaf)) (.n 8 7 (.n 5 14 .leaf .leaf) .leaf)) (.n 28 19 (.n 26 4 (.n 17 7 .leaf .leaf) .leaf) (.n 30 23 (.n 29 13 .leaf .leaf) .leaf))) (.n 42 9 (.n 35 6 (.n 33 9 (.n 32 13 .leaf .leaf) (.n 34 9 .leaf .leaf)) (.n 41 13 (.n 39 14 .leaf .leaf) .leaf)) (.n 51 3 (.n 44 6 (.n 43 9 .leaf .leaf) .leaf) (.n 53 3 (.n 52 3 .leaf .leaf) .leaf)))) (.n 122 8 (.n 79 4 (.n 69 7 (.n 61 7 (.n 60 7 .leaf .leaf) (.n 66 2 .leaf .leaf)) (.n 78 4 (.n 70 7 .leaf .leaf) .leaf)) (.n 116 5 (.n 113 8 (.n 112 3 .leaf .leaf) .leaf) (.n 119 8 (.n 118 9 .leaf .leaf) .leaf))) (.n 134 2 (.n 128 2 (.n 127 2 (.n 125 5 .leaf .leaf) .leaf) (.n 131 2 (.n 130 2 .leaf .leaf) .leaf)) (.n 151 7 (.n 150 7 (.n 142 7 .leaf .leaf) .leaf) (.n 157 7 (.n 156 7 .leaf .leaf) .leaf))))) (.n 798 6 (.n 768 13 (.n 759 17 (.n 403 4 (.n 238 4 (.n 160 4 .leaf .leaf) (.n 394 7 .leaf .leaf)) (.n 758 12 (.n 757 11 .leaf .leaf) .leaf)) (.n 762 5 (.n 761 12 (.n 760 6 .leaf .leaf) .leaf) (.n 764 5 (.n 763 5 .leaf .leaf) .leaf))) (.n 782 3 (.n 773 5 (.n 771 5 (.n 770 12 .leaf .leaf) (.n 772 5 .leaf .leaf)) (.n 781 3 (.n 780 3 .leaf .leaf) .leaf)) (.n 789 6 (.n 787 7 (.n 786 8 .leaf .leaf) .leaf) (.n 795 2 (.n 790 6 .leaf .leaf) .leaf)))) (.n 829 8 (.n 819 17 (.n 814 9 (.n 807 3 (.n 799 6 .leaf .leaf) (.n 808 3 .leaf .leaf)) (.n 818 5 (.n 815 8 .leaf .leaf) .leaf)) (.n 824 8 (.n 821 8 (.n 820 9 .leaf .leaf) .leaf) (.n 828 8 (.n 827 5 .leaf .leaf) .leaf))) (.n 842 7 (.n 833 3 (.n 832 8 (.n 830 3 .leaf .leaf) .leaf) (.n 841 3 (.n 836 3 .leaf .leaf) .leaf)) (.n 845 4 (.n 844 4 (.n 843 4 .leaf .leaf) .leaf) (.n 848 7 (.n 847 5 .leaf .leaf) .leaf)))))) (.n 1122 6 (.n 905 6 (.n 863 2 (.n 857 2 (.n 854 4 (.n 852 4 (.n 851 7 .leaf .leaf) (.n 853 4 .leaf .leaf)) (.n 856 2 (.n 855 2 .leaf .leaf) .leaf)) (.n 860 2 (.n 859 2 (.n 858 2 .leaf .leaf) .leaf) (.n 862 2 (.n 861 2 .leaf .leaf) .leaf))) (.n 883 6 (.n 879 6 (.n 871 6 (.n 870 6 .leaf .leaf) (.n 876 2 .leaf .leaf)) (.n 882 6 (.n 880 6 .leaf .leaf) .leaf)) (.n 888 3 (.n 886 6 (.n 885 6 .leaf .leaf) .leaf) (.n 903 7 (.n 889 3 .leaf .leaf) .leaf)))) (.n 941 3 (.n 930 7 (.n 912 3 (.n 910 3 (.n 909 3 .leaf .leaf) (.n 911 3 .leaf .leaf)) (.n 914 3 (.n 913 3 .leaf .leaf) .leaf)) (.n 938 3 (.n 937 3 (.n 932 6 .leaf .leaf) .leaf) (.n 940 3 (.n 939 3 .leaf .leaf) .leaf))) (.n 1068 7 (.n 967 3 (.n 966 3 (.n 957 2 .leaf .leaf) .leaf) (.n 1067 2 (.n 1065 3 .leaf .leaf) .leaf)) (.n 1077 3 (.n 1070 2 (.n 1069 7 .leaf .leaf) .leaf) (.n 1079 2 (.n 1078 3 .leaf .leaf) .leaf))))) (.n 1666 4 (.n 1578 2 (.n 1183 3 (.n 1155 3 (.n 1131 3 (.n 1123 6 .leaf .leaf) (.n 1132 3 .leaf .leaf)) (.n 1157 3 (.n 1156 3 .leaf .leaf) .leaf)) (.n 1572 5 (.n 1570 3 (.n 1184 3 .leaf .leaf) .leaf) (.n 1576 6 (.n 1573 5 .leaf .leaf) .leaf))) (.n 1590 2 (.n 1585 2 (.n 1582 5 (.n 1581 5 .leaf .leaf) (.n 1584 2 .leaf .leaf)) (.n 1588 2 (.n 1587 2 .leaf .leaf) .leaf)) (.n 1639 4 (.n 1638 4 (.n 1591 2 .leaf .leaf) .leaf) (.n 1659 2 (.n 1642 4 .leaf .leaf) .leaf)))) (.n 3032 3 (.n 1807 2 (.n 1797 2 (.n 1669 4 (.n 1668 4 .leaf .leaf) (.n 1794 2 .leaf .leaf)) (.n 1806 2 (.n 1798 2 .leaf .leaf) .leaf)) (.n 1912 4 (.n 1885 4 (.n 1884 4 .leaf .leaf) .leaf) (.n 3029 3 (.n 3028 3 .leaf .leaf) .leaf))) (.n 3044 2 (.n 3038 3 (.n 3035 3 (.n 3034 3 .leaf .leaf) .leaf) (.n 3043 2 (.n 3041 3 .leaf .leaf) .leaf)) (.n 3050 2 (.n 3047 2 (.n 3046 2 .leaf .leaf) .leaf) (.n 3061 6 (.n 3058 5 .leaf .leaf) .leaf))))))) (.n 20539 2 (.n 20454 5 (.n 3310 5 (.n 3201 2 (.n 3076 2 (.n 3072 2 (.n 3067 5 (.n 3066 5 .leaf .leaf) (.n 3070 2 .leaf .leaf)) (.n 3075 2 (.n 3073 2 .leaf .leaf) .leaf)) (.n 3154 2 (.n 3151 2 (.n 3142 2 .leaf .leaf) .leaf) (.n 3200 6 (.n 3198 7 .leaf .leaf) .leaf))) (.n 3229 5 (.n 3211 2 (.n 3203 2 (.n 3202 2 .leaf .leaf) (.n 3210 2 .leaf .leaf)) (.n 3228 5 (.n 3212 2 .leaf .leaf) .leaf)) (.n 3235 2 (.n 3234 2 (.n 3232 2 .leaf .leaf) .leaf) (.n 3238 2 (.n 3237 2 .leaf .leaf) .leaf)))) (.n 4099 4 (.n 3397 2 (.n 3318 2 (.n 3315 2 (.n 3313 2 .leaf .leaf) (.n 3316 2 .leaf .leaf)) (.n 3394 2 (.n 3319 2 .leaf .leaf) .leaf)) (.n 4069 4 (.n 3856 4 (.n 3853 4 .leaf .leaf) .leaf) (.n 4098 4 (.n 4072 4 .leaf .leaf) .leaf))) (.n 20444 11 (.n 20441 11 (.n 20440 11 (.n 10660 4 .leaf .leaf) .leaf) (.n 20443 6 (.n 20442 11 .leaf .leaf) .leaf)) (.n 20447 5 (.n 20446 5 (.n 20445 5 .leaf .leaf) .leaf) (.n 20453 11 (.n 20451 11 .leaf .leaf) .leaf))))) (.n 20508 5 (.n 20490 3 (.n 20470 6 (.n 20464 3 (.n 20456 5 (.n 20455 5 .leaf .leaf) (.n 20463 3 .leaf .leaf)) (.n 20469 7 (.n 20465 3 .leaf .leaf) .leaf)) (.n 20478 2 (.n 20473 5 (.n 20472 5 .leaf .leaf) .leaf) (.n 20482 5 (.n 20481 5 .leaf .leaf) .leaf))) (.n 20501 5 (.n 20498 7 (.n 20496 13 (.n 20491 3 .leaf .leaf) (.n 20497 6 .leaf .leaf)) (.n 20500 5 (.n 20499 5 .leaf .leaf) .leaf)) (.n 20504 7 (.n 20503 6 (.n 20502 13 .leaf .leaf) .leaf) (.n 20507 7 (.n 20505 8 .leaf .leaf) .leaf)))) (.n 20525 6 (.n 20515 5 (.n 20512 5 (.n 20510 5 (.n 20509 5 .leaf .leaf) (.n 20511 5 .leaf .leaf)) (.n 20514 5 (.n 20513 3 .leaf .leaf) .leaf)) (.n 20518 3 (.n 20517 3 (.n 20516 3 .leaf .leaf) .leaf) (.n 20524 3 (.n 20519 3 .leaf .leaf) .leaf))) (.n 20532 6 (.n 20528 4 (.n 20527 4 (.n 20526 4 .leaf .leaf) .leaf) (.n 20531 6 (.n 20530 5 .leaf .leaf) .leaf)) (.n 20536 4 (.n 20535 4 (.n 20534 6 .leaf .leaf) .leaf) (.n 20538 2 (.n 20537 4 .leaf .leaf) .leaf)))))) (.n 20840 3 (.n 20597 3 (.n 20565 5 (.n 20546 2 (.n 20543 2 (.n 20541 2 (.n 20540 2 .leaf .leaf) (.n 20542 2 .leaf .leaf)) (.n 20545 2 (.n 20544 2 .leaf .leaf) .leaf)) (.n 20559 2 (.n 20554 5 (.n 20553 5 .leaf .leaf) .leaf) (.n 20563 5 (.n 20562 5 .leaf .leaf) .leaf))) (.n 20588 5 (.n 20571 3 (.n 20568 5 (.n 20566 5 .leaf .leaf) (.n 20569 5 .leaf .leaf)) (.n 20586 5 (.n 20572 3 .leaf .leaf) .leaf)) (.n 20594 3 (.n 20593 3 (.n 20592 3 .leaf .leaf) .leaf) (.n 20596 3 (.n 20595 3 .leaf .leaf) .leaf)))) (.n 20751 5 (.n 20624 3 (.n 20621 3 (.n 20615 5 (.n 20613 5 .leaf .leaf) (.n 20620 3 .leaf .leaf)) (.n 20623 3 (.n 20622 3 .leaf .leaf) .leaf)) (.n 20650 3 (.n 20649 3 (.n 20640 2 .leaf .leaf) .leaf) (.n 20750 2 (.n 20748 3 .leaf .leaf) .leaf))) (.n 20805 5 (.n 20760 3 (.n 20753 2 (.n 20752 5 .leaf .leaf) .leaf) (.n 20762 2 (.n 20761 3 .leaf .leaf) .leaf)) (.n 20815 3 (.n 20814 3 (.n 20806 5 .leaf .leaf) .leaf) (.n 20839 3 (.n 20838 3 .leaf .leaf) .leaf))))) (.n 21270 2 (.n 21243 3 (.n 21232 6 (.n 21228 5 (.n 20867 3 (.n 20866 3 .leaf .leaf) (.n 21226 4 .leaf .leaf)) (.n 21231 7 (.n 21229 5 .leaf .leaf) .leaf)) (.n 21238 5 (.n 21237 5 (.n 21234 2 .leaf .leaf) .leaf) (.n 21241 3 (.n 21240 3 .leaf .leaf) .leaf))) (.n 21259 5 (.n 21253 3 (.n 21246 3 (.n 21244 3 .leaf .leaf) (.n 21247 3 .leaf .leaf)) (.n 21256 4 (.n 21255 4 .leaf .leaf) .leaf)) (.n 21265 4 (.n 21264 4 (.n 21261 2 .leaf .leaf) .leaf) (.n 21268 2 (.n 21267 2 .leaf .leaf) .leaf)))) (.n 21477 2 (.n 21324 3 (.n 21315 2 (.n 21273 2 (.n 21271 2 .leaf .leaf) (.n 21274 2 .leaf .leaf)) (.n 21322 3 (.n 21321 3 .leaf .leaf) .leaf)) (.n 21349 3 (.n 21342 2 (.n 21325 3 .leaf .leaf) .leaf) (.n 21352 3 (.n 21351 3 .leaf .leaf) .leaf))) (.n 21568 3 (.n 21489 2 (.n 21481 2 (.n 21480 2 .leaf .leaf) .leaf) (.n 21567 3 (.n 21490 2 .leaf .leaf) .leaf)) (.n 21983 4 (.n 21982 3 (.n 21595 3 .leaf .leaf) .leaf) (.n 21987 8 (.n 21986 4 .leaf .leaf) .leaf)))))))) (.n 23782 3 (.n 22780 2 (.n 22189 3 (.n 22108 3 (.n 22017 2 (.n 22000 2 (.n 21996 2 (.n 21992 4 (.n 21989 4 .leaf .leaf) (.n 21995 4 .leaf .leaf)) (.n 21998 2 (.n 21997 2 .leaf .leaf) .leaf)) (.n 22012 5 (.n 22004 2 (.n 22001 2 .leaf .leaf) .leaf) (.n 22015 6 (.n 22014 7 .leaf .leaf) .leaf))) (.n 22029 3 (.n 22024 3 (.n 22021 5 (.n 22020 5 .leaf .leaf) (.n 22023 3 .leaf .leaf)) (.n 22027 3 (.n 22026 3 .leaf .leaf) .leaf)) (.n 22096 2 (.n 22095 3 (.n 22030 3 .leaf .leaf) .leaf) (.n 22105 3 (.n 22104 3 .leaf .leaf) .leaf)))) (.n 22160 3 (.n 22154 6 (.n 22150 3 (.n 22130 3 (.n 22127 7 .leaf .leaf) (.n 22139 3 .leaf .leaf)) (.n 22152 7 (.n 22151 6 .leaf .leaf) .leaf)) (.n 22157 2 (.n 22156 2 (.n 22155 2 .leaf .leaf) .leaf) (.n 22159 4 (.n 22158 4 .leaf .leaf) .leaf))) (.n 22166 2 (.n 22163 3 (.n 22162 4 (.n 22161 4 .leaf .leaf) .leaf) (.n 22165 2 (.n 22164 2 .leaf .leaf) .leaf)) (.n 22185 3 (.n 22183 5 (.n 22182 5 .leaf .leaf) .leaf) (.n 22188 3 (.n 22186 3 .leaf .leaf) .leaf))))) (.n 22726 2 (.n 22711 3 (.n 22270 3 (.n 22266 3 (.n 22192 3 (.n 22191 3 .leaf .leaf) (.n 22264 5 .leaf .leaf)) (.n 22269 3 (.n 22267 3 .leaf .leaf) .leaf)) (.n 22347 3 (.n 22273 3 (.n 22272 3 .leaf .leaf) .leaf) (.n 22351 3 (.n 22348 3 .leaf .leaf) .leaf))) (.n 22719 3 (.n 22715 3 (.n 22713 3 (.n 22712 3 .leaf .leaf) (.n 22714 3 .leaf .leaf)) (.n 22718 3 (.n 22717 3 .leaf .leaf) .leaf)) (.n 22723 3 (.n 22722 3 (.n 22721 3 .leaf .leaf) .leaf) (.n 22725 2 (.n 22724 3 .leaf .leaf) .leaf)))) (.n 22750 4 (.n 22733 2 (.n 22730 2 (.n 22728 2 (.n 22727 2 .leaf .leaf) (.n 22729 2 .leaf .leaf)) (.n 22732 2 (.n 22731 2 .leaf .leaf) .leaf)) (.n 22744 5 (.n 22741 4 (.n 22740 4 .leaf .leaf) .leaf) (.n 22749 4 (.n 22746 2 .leaf .leaf) .leaf))) (.n 22759 2 (.n 22755 2 (.n 22753 2 (.n 22752 2 .leaf .leaf) .leaf) (.n 22758 2 (.n 22756 2 .leaf .leaf) .leaf)) (.n 22773 4 (.n 22772 4 (.n 22771 2 .leaf .leaf) .leaf) (.n 22779 2 (.n 22775 4 .leaf .leaf) .leaf)))))) (.n 22949 2 (.n 22893 2 (.n 22810 2 (.n 22800 4 (.n 22784 2 (.n 22782 2 (.n 22781 2 .leaf .leaf) (.n 22783 2 .leaf .leaf)) (.n 22799 4 (.n 22798 2 .leaf .leaf) .leaf)) (.n 22807 2 (.n 22806 2 (.n 22802 4 .leaf .leaf) .leaf) (.n 22809 2 (.n 22808 2 .leaf .leaf) .leaf))) (.n 22837 2 (.n 22833 2 (.n 22825 2 (.n 22811 2 .leaf .leaf) (.n 22827 2 .leaf .leaf)) (.n 22836 2 (.n 22834 2 .leaf .leaf) .leaf)) (.n 22884 2 (.n 22883 5 (.n 22881 5 .leaf .leaf) .leaf) (.n 22886 2 (.n 22885 2 .leaf .leaf) .leaf)))) (.n 22937 2 (.n 22915 2 (.n 22911 4 (.n 22895 2 (.n 22894 2 .leaf .leaf) (.n 22908 2 .leaf .leaf)) (.n 22914 2 (.n 22912 4 .leaf .leaf) .leaf)) (.n 22920 2 (.n 22918 2 (.n 22917 2 .leaf .leaf) .leaf) (.n 22935 3 (.n 22921 2 .leaf .leaf) .leaf))) (.n 22943 2 (.n 22940 2 (.n 22939 4 (.n 22938 4 .leaf .leaf) .leaf) (.n 22942 2 (.n 22941 2 .leaf .leaf) .leaf)) (.n 22946 2 (.n 22945 2 (.n 22944 2 .leaf .leaf) .leaf) (.n 22948 2 (.n 22947 2 .leaf .leaf) .leaf))))) (.n 23508 3 (.n 23026 2 (.n 23001 2 (.n 22996 2 (.n 22993 4 (.n 22992 4 .leaf .leaf) (.n 22995 2 .leaf .leaf)) (.n 22999 2 (.n 22998 2 .leaf .leaf) .leaf)) (.n 23023 2 (.n 23022 2 (.n 23002 2 .leaf .leaf) .leaf) (.n 23025 2 (.n 23024 2 .leaf .leaf) .leaf))) (.n 23054 2 (.n 23051 2 (.n 23049 2 (.n 23027 2 .leaf .leaf) (.n 23050 2 .leaf .leaf)) (.n 23053 2 (.n 23052 2 .leaf .leaf) .leaf)) (.n 23079 2 (.n 23077 2 (.n 23076 2 .leaf .leaf) .leaf) (.n 23502 2 (.n 23080 2 .leaf .leaf) .leaf)))) (.n 23671 2 (.n 23538 3 (.n 23529 2 (.n 23511 3 (.n 23509 3 .leaf .leaf) (.n 23512 3 .leaf .leaf)) (.n 23536 3 (.n 23535 3 .leaf .leaf) .leaf)) (.n 23667 2 (.n 23664 2 (.n 23539 3 .leaf .leaf) .leaf) (.n 23670 2 (.n 23668 2 .leaf .leaf) .leaf))) (.n 23752 3 (.n 23676 2 (.n 23674 2 (.n 23673 2 .leaf .leaf) .leaf) (.n 23751 3 (.n 23677 2 .leaf .leaf) .leaf)) (.n 23778 3 (.n 23755 3 (.n 23754 3 .leaf .leaf) .leaf) (.n 23781 3 (.n 23779 3 .leaf .leaf) .leaf))))))) (.n 48568 2 (.n 42405 3 (.n 28767 3 (.n 25122 3 (.n 24403 3 (.n 24400 3 (.n 24395 2 (.n 24393 3 .leaf .leaf) (.n 24399 3 .leaf .leaf)) (.n 24402 3 (.n 24401 2 .leaf .leaf) .leaf)) (.n 24454 3 (.n 24453 3 (.n 24404 2 .leaf .leaf) .leaf) (.n 24457 3 (.n 24456 3 .leaf .leaf) .leaf))) (.n 25183 3 (.n 25131 3 (.n 25129 3 (.n 25124 2 .leaf .leaf) (.n 25130 2 .leaf .leaf)) (.n 25133 2 (.n 25132 3 .leaf .leaf) .leaf)) (.n 25851 2 (.n 25186 3 (.n 25185 3 .leaf .leaf) .leaf) (.n 25861 2 (.n 25860 2 .leaf .leaf) .leaf)))) (.n 28858 3 (.n 28781 2 (.n 28772 2 (.n 28770 3 (.n 28769 2 .leaf .leaf) (.n 28771 3 .leaf .leaf)) (.n 28780 3 (.n 28779 3 .leaf .leaf) .leaf)) (.n 28833 2 (.n 28825 2 (.n 28824 2 .leaf .leaf) .leaf) (.n 28857 3 (.n 28834 2 .leaf .leaf) .leaf))) (.n 30343 3 (.n 28886 2 (.n 28885 3 (.n 28859 2 .leaf .leaf) .leaf) (.n 30316 3 (.n 30315 3 .leaf .leaf) .leaf)) (.n 42397 3 (.n 42396 3 (.n 42394 3 .leaf .leaf) .leaf) (.n 42402 2 (.n 42400 3 .leaf .leaf) .leaf))))) (.n 42624 2 (.n 42483 2 (.n 42415 2 (.n 42411 2 (.n 42408 2 (.n 42406 3 .leaf .leaf) (.n 42409 2 .leaf .leaf)) (.n 42414 2 (.n 42412 2 .leaf .leaf) .leaf)) (.n 42463 2 (.n 42462 2 (.n 42454 2 .leaf .leaf) .leaf) (.n 42481 2 (.n 42466 2 .leaf .leaf) .leaf))) (.n 42568 2 (.n 42493 2 (.n 42490 2 (.n 42489 2 .leaf .leaf) (.n 42492 2 .leaf .leaf)) (.n 42567 2 (.n 42564 2 .leaf .leaf) .leaf)) (.n 42618 2 (.n 42577 2 (.n 42576 2 .leaf .leaf) .leaf) (.n 42622 2 (.n 42621 2 .leaf .leaf) .leaf)))) (.n 42736 2 (.n 42706 2 (.n 42630 2 (.n 42627 2 (.n 42625 2 .leaf .leaf) (.n 42628 2 .leaf .leaf)) (.n 42705 2 (.n 42631 2 .leaf .leaf) .leaf)) (.n 42732 2 (.n 42709 2 (.n 42708 2 .leaf .leaf) .leaf) (.n 42735 2 (.n 42733 2 .leaf .leaf) .leaf))) (.n 48453 2 (.n 44814 2 (.n 44812 2 (.n 44805 2 .leaf .leaf) .leaf) (.n 48450 2 (.n 44815 2 .leaf .leaf) .leaf)) (.n 48463 2 (.n 48462 2 (.n 48454 2 .leaf .leaf) .leaf) (.n 48541 2 (.n 48540 2 .leaf .leaf) .leaf)))))) (.n 82048 2 (.n 81928 3 (.n 81790 3 (.n 81773 3 (.n 81766 3 (.n 81761 3 (.n 81760 3 .leaf .leaf) (.n 81764 3 .leaf .leaf)) (.n 81770 3 (.n 81767 3 .leaf .leaf) .leaf)) (.n 81778 2 (.n 81776 2 (.n 81775 2 .leaf .leaf) .leaf) (.n 81782 2 (.n 81779 2 .leaf .leaf) .leaf))) (.n 81805 2 (.n 81799 3 (.n 81795 2 (.n 81793 3 .leaf .leaf) (.n 81798 3 .leaf .leaf)) (.n 81804 2 (.n 81802 2 .leaf .leaf) .leaf)) (.n 81874 2 (.n 81808 2 (.n 81807 2 .leaf .leaf) .leaf) (.n 81886 2 (.n 81883 2 .leaf .leaf) .leaf)))) (.n 81943 2 (.n 81937 2 (.n 81933 2 (.n 81930 3 (.n 81929 3 .leaf .leaf) (.n 81932 3 .leaf .leaf)) (.n 81935 2 (.n 81934 2 .leaf .leaf) .leaf)) (.n 81940 2 (.n 81939 2 (.n 81938 2 .leaf .leaf) .leaf) (.n 81942 2 (.n 81941 2 .leaf .leaf) .leaf))) (.n 81967 2 (.n 81961 3 (.n 81960 3 (.n 81944 2 .leaf .leaf) .leaf) (.n 81966 2 (.n 81964 2 .leaf .leaf) .leaf)) (.n 82042 3 (.n 81970 2 (.n 81969 2 .leaf .leaf) .leaf) (.n 82047 2 (.n 82045 2 .leaf .leaf) .leaf))))) (.n 82828 2 (.n 82669 2 (.n 82588 2 (.n 82129 2 (.n 82051 2 (.n 82050 2 .leaf .leaf) (.n 82126 2 .leaf .leaf)) (.n 82585 2 (.n 82576 2 .leaf .leaf) .leaf)) (.n 82663 2 (.n 82662 2 (.n 82659 2 .leaf .leaf) .leaf) (.n 82668 2 (.n 82666 2 .leaf .leaf) .leaf))) (.n 82723 2 (.n 82717 2 (.n 82672 2 (.n 82671 2 .leaf .leaf) .leaf) (.n 82722 2 (.n 82720 2 .leaf .leaf) .leaf)) (.n 82801 2 (.n 82726 2 (.n 82725 2 .leaf .leaf) .leaf) (.n 82804 2 (.n 82803 2 .leaf .leaf) .leaf)))) (.n 86448 2 (.n 86363 2 (.n 84855 2 (.n 82831 2 (.n 82830 2 .leaf .leaf) (.n 84846 2 .leaf .leaf)) (.n 86360 2 (.n 84856 2 .leaf .leaf) .leaf)) (.n 86416 2 (.n 86415 2 (.n 86372 2 .leaf .leaf) .leaf) (.n 86425 2 (.n 86424 2 .leaf .leaf) .leaf))) (.n 87178 2 (.n 86476 2 (.n 86450 2 (.n 86449 2 .leaf .leaf) .leaf) (.n 87175 2 (.n 86477 2 .leaf .leaf) .leaf)) (.n 87205 2 (.n 87204 2 (.n 87202 2 .leaf .leaf) .leaf) (.n 89392 2 (.n 89389 2 .leaf .leaf) .leaf)))))))))

/-! ## 2. Pure-Lean Fin 3 / Fin 4 helpers and 4×3 grid representation -/

private def vec4 {α : Type} (a0 a1 a2 a3 : α) : Fin 4 → α
  | ⟨0, _⟩ => a0
  | ⟨1, _⟩ => a1
  | ⟨2, _⟩ => a2
  | ⟨3, _⟩ => a3

private def vec3 {α : Type} (a0 a1 a2 : α) : Fin 3 → α
  | ⟨0, _⟩ => a0
  | ⟨1, _⟩ => a1
  | ⟨2, _⟩ => a2

private abbrev Grid := Fin 4 → Fin 3 → Nat

private def tritVal : Option Bool → Nat
  | none => 0
  | some false => 1
  | some true => 2

private def toGrid (ρ : Nat → Option Bool) : Grid :=
  fun p h => tritVal (ρ (p.val * 3 + h.val))

private def rowCode (r : Fin 3 → Nat) : Nat :=
  r ⟨0, by decide⟩ + 3 * r ⟨1, by decide⟩ + 9 * r ⟨2, by decide⟩

private def pack4 (r0 r1 r2 r3 : Nat) : Nat :=
  ((r0 * 27 + r1) * 27 + r2) * 27 + r3

private def packGrid (g : Grid) : Nat :=
  pack4 (rowCode (g ⟨0, by decide⟩)) (rowCode (g ⟨1, by decide⟩))
        (rowCode (g ⟨2, by decide⟩)) (rowCode (g ⟨3, by decide⟩))

private def rowTwos (r : Nat) : Nat :=
  (if r % 3 == 2 then 1 else 0) +
  (if (r / 3) % 3 == 2 then 2 else 0) +
  (if r / 9 == 2 then 4 else 0)

private def hasColClash (m0 m1 m2 m3 : Nat) : Bool :=
  ((m0 &&& m1) != 0) || (((m0 ||| m1) &&& m2) != 0) || (((m0 ||| m1 ||| m2) &&& m3) != 0)

private def isFalsifiedRows (r0 r1 r2 r3 : Nat) : Bool :=
  r0 == 13 || r1 == 13 || r2 == 13 || r3 == 13 ||
  hasColClash (rowTwos r0) (rowTwos r1) (rowTwos r2) (rowTwos r3)

private def isFalsified (g : Grid) : Bool :=
  isFalsifiedRows (rowCode (g ⟨0, by decide⟩)) (rowCode (g ⟨1, by decide⟩))
                  (rowCode (g ⟨2, by decide⟩)) (rowCode (g ⟨3, by decide⟩))

private def permRow (r h0 h1 h2 : Nat) : Nat :=
  let c0 := r % 3
  let c1 := (r / 3) % 3
  let c2 := r / 9
  let get (h : Nat) := if h == 0 then c0 else if h == 1 then c1 else c2
  get h0 + 3 * get h1 + 9 * get h2

@[inline] private def cmpSwap {α : Type} (x y : Nat) (k : Nat → Nat → α) : α :=
  if x ≤ y then k x y else k y x

private def sort4Pack (a0 a1 a2 a3 : Nat) : Nat :=
  cmpSwap a0 a1 fun b0 b1 =>
  cmpSwap a2 a3 fun b2 b3 =>
  cmpSwap b0 b2 fun c0 c2 =>
  cmpSwap b1 b3 fun c1 c3 =>
  cmpSwap c1 c2 fun d1 d2 =>
  pack4 c0 d1 d2 c3

private def canonRows (r0 r1 r2 r3 : Nat) : Nat :=
  let v0 := sort4Pack (permRow r0 0 1 2) (permRow r1 0 1 2) (permRow r2 0 1 2) (permRow r3 0 1 2)
  let v1 := sort4Pack (permRow r0 0 2 1) (permRow r1 0 2 1) (permRow r2 0 2 1) (permRow r3 0 2 1)
  let v2 := sort4Pack (permRow r0 1 0 2) (permRow r1 1 0 2) (permRow r2 1 0 2) (permRow r3 1 0 2)
  let v3 := sort4Pack (permRow r0 1 2 0) (permRow r1 1 2 0) (permRow r2 1 2 0) (permRow r3 1 2 0)
  let v4 := sort4Pack (permRow r0 2 0 1) (permRow r1 2 0 1) (permRow r2 2 0 1) (permRow r3 2 0 1)
  let v5 := sort4Pack (permRow r0 2 1 0) (permRow r1 2 1 0) (permRow r2 2 1 0) (permRow r3 2 1 0)
  Nat.min v0 (Nat.min v1 (Nat.min v2 (Nat.min v3 (Nat.min v4 v5))))

private def canon (g : Grid) : Nat :=
  canonRows (rowCode (g ⟨0, by decide⟩)) (rowCode (g ⟨1, by decide⟩))
            (rowCode (g ⟨2, by decide⟩)) (rowCode (g ⟨3, by decide⟩))

private def lbRows (r0 r1 r2 r3 : Nat) : Nat :=
  if isFalsifiedRows r0 r1 r2 r3 then 1 else dpBST.find (canonRows r0 r1 r2 r3)

private def lb (g : Grid) : Nat :=
  lbRows (rowCode (g ⟨0, by decide⟩)) (rowCode (g ⟨1, by decide⟩))
         (rowCode (g ⟨2, by decide⟩)) (rowCode (g ⟨3, by decide⟩))

private def setCell (g : Grid) (p : Fin 4) (h : Fin 3) (v : Nat) : Grid :=
  fun p' h' => if p' = p ∧ h' = h then v else g p' h'

/-! ## 3. Group S_4 × S_3 and invariance of `isFalsified` and `canon` -/

private def perm4Fn (pi : Fin 24) : Fin 4 → Fin 4 :=
  match pi.val with
  | 0  => vec4 0 1 2 3
  | 1  => vec4 0 1 3 2
  | 2  => vec4 0 2 1 3
  | 3  => vec4 0 2 3 1
  | 4  => vec4 0 3 1 2
  | 5  => vec4 0 3 2 1
  | 6  => vec4 1 0 2 3
  | 7  => vec4 1 0 3 2
  | 8  => vec4 1 2 0 3
  | 9  => vec4 1 2 3 0
  | 10 => vec4 1 3 0 2
  | 11 => vec4 1 3 2 0
  | 12 => vec4 2 0 1 3
  | 13 => vec4 2 0 3 1
  | 14 => vec4 2 1 0 3
  | 15 => vec4 2 1 3 0
  | 16 => vec4 2 3 0 1
  | 17 => vec4 2 3 1 0
  | 18 => vec4 3 0 1 2
  | 19 => vec4 3 0 2 1
  | 20 => vec4 3 1 0 2
  | 21 => vec4 3 1 2 0
  | 22 => vec4 3 2 0 1
  | _  => vec4 3 2 1 0

private def perm3Fn : Fin 6 → Fin 3 → Fin 3
  | ⟨0, _⟩ => vec3 0 1 2
  | ⟨1, _⟩ => vec3 0 2 1
  | ⟨2, _⟩ => vec3 1 0 2
  | ⟨3, _⟩ => vec3 1 2 0
  | ⟨4, _⟩ => vec3 2 0 1
  | ⟨5, _⟩ => vec3 2 1 0

private def permGrid (pi : Fin 24) (si : Fin 6) (g : Grid) : Grid :=
  fun p h => g (perm4Fn pi p) (perm3Fn si h)

private def validGrid (g : Grid) : Prop :=
  ∀ (p : Fin 4) (h : Fin 3), g p h < 3

private theorem rowCode_lt {r : Fin 3 → Nat} (hr : ∀ h, r h < 3) : rowCode r < 27 := by
  have h0 := hr ⟨0, by decide⟩; have h1 := hr ⟨1, by decide⟩; have h2 := hr ⟨2, by decide⟩
  unfold rowCode; omega

private theorem permRow_eq {r : Fin 3 → Nat} (hr : ∀ h, r h < 3) (h0 h1 h2 : Fin 3) :
    permRow (rowCode r) h0.val h1.val h2.val = r h0 + 3 * r h1 + 9 * r h2 := by
  have c0 := hr ⟨0, by decide⟩; have c1 := hr ⟨1, by decide⟩; have c2 := hr ⟨2, by decide⟩
  have e0 : rowCode r % 3 = r ⟨0, by decide⟩ := by unfold rowCode; omega
  have e1 : (rowCode r / 3) % 3 = r ⟨1, by decide⟩ := by unfold rowCode; omega
  have e2 : rowCode r / 9 = r ⟨2, by decide⟩ := by unfold rowCode; omega
  unfold permRow
  rw [e0, e1, e2]
  match h0, h1, h2 with
  | ⟨0, _⟩, ⟨0, _⟩, ⟨0, _⟩ | ⟨0, _⟩, ⟨0, _⟩, ⟨1, _⟩ | ⟨0, _⟩, ⟨0, _⟩, ⟨2, _⟩
  | ⟨0, _⟩, ⟨1, _⟩, ⟨0, _⟩ | ⟨0, _⟩, ⟨1, _⟩, ⟨1, _⟩ | ⟨0, _⟩, ⟨1, _⟩, ⟨2, _⟩
  | ⟨0, _⟩, ⟨2, _⟩, ⟨0, _⟩ | ⟨0, _⟩, ⟨2, _⟩, ⟨1, _⟩ | ⟨0, _⟩, ⟨2, _⟩, ⟨2, _⟩
  | ⟨1, _⟩, ⟨0, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨0, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨0, _⟩, ⟨2, _⟩
  | ⟨1, _⟩, ⟨1, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨1, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨1, _⟩, ⟨2, _⟩
  | ⟨1, _⟩, ⟨2, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨2, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨2, _⟩, ⟨2, _⟩
  | ⟨2, _⟩, ⟨0, _⟩, ⟨0, _⟩ | ⟨2, _⟩, ⟨0, _⟩, ⟨1, _⟩ | ⟨2, _⟩, ⟨0, _⟩, ⟨2, _⟩
  | ⟨2, _⟩, ⟨1, _⟩, ⟨0, _⟩ | ⟨2, _⟩, ⟨1, _⟩, ⟨1, _⟩ | ⟨2, _⟩, ⟨1, _⟩, ⟨2, _⟩
  | ⟨2, _⟩, ⟨2, _⟩, ⟨0, _⟩ | ⟨2, _⟩, ⟨2, _⟩, ⟨1, _⟩ | ⟨2, _⟩, ⟨2, _⟩, ⟨2, _⟩ => rfl

private def sort4Tuple (a0 a1 a2 a3 : Nat) : Nat × Nat × Nat × Nat :=
  cmpSwap a0 a1 fun b0 b1 =>
  cmpSwap a2 a3 fun b2 b3 =>
  cmpSwap b0 b2 fun c0 c2 =>
  cmpSwap b1 b3 fun c1 c3 =>
  cmpSwap c1 c2 fun d1 d2 =>
  (c0, d1, d2, c3)

private theorem cmpSwap_map {α β : Type} (f : α → β) (x y : Nat) (k : Nat → Nat → α) :
    f (cmpSwap x y k) = cmpSwap x y (fun u v => f (k u v)) := by
  unfold cmpSwap; split <;> rfl

private theorem cmpSwap_cases {α : Type} (x y : Nat) (k : Nat → Nat → α) {P : α → Prop}
    (h1 : x ≤ y → P (k x y)) (h2 : ¬x ≤ y → P (k y x)) : P (cmpSwap x y k) := by
  unfold cmpSwap; split
  · exact h1 ‹_›
  · exact h2 ‹_›

private theorem sort4Pack_eq (a0 a1 a2 a3 : Nat) :
    sort4Pack a0 a1 a2 a3 =
      pack4 (sort4Tuple a0 a1 a2 a3).1 (sort4Tuple a0 a1 a2 a3).2.1
            (sort4Tuple a0 a1 a2 a3).2.2.1 (sort4Tuple a0 a1 a2 a3).2.2.2 := by
  let f : Nat × Nat × Nat × Nat → Nat := fun t => pack4 t.1 t.2.1 t.2.2.1 t.2.2.2
  change sort4Pack a0 a1 a2 a3 = f (sort4Tuple a0 a1 a2 a3)
  unfold sort4Pack sort4Tuple
  simp only [cmpSwap_map f]
  rfl

private theorem pack4_le_of_sorted {b0 b1 b2 b3 : Nat}
    (hb : b0 ≤ b1 ∧ b1 ≤ b2 ∧ b2 ≤ b3)
    (pi : Fin 24) :
    let f := vec4 b0 b1 b2 b3
    pack4 b0 b1 b2 b3 ≤
      pack4 (f (perm4Fn pi ⟨0, by decide⟩)) (f (perm4Fn pi ⟨1, by decide⟩))
            (f (perm4Fn pi ⟨2, by decide⟩)) (f (perm4Fn pi ⟨3, by decide⟩)) := by
  rcases pi with ⟨n, hn⟩
  match n with
  | 0  | 1  | 2  | 3  | 4  | 5
  | 6  | 7  | 8  | 9  | 10 | 11
  | 12 | 13 | 14 | 15 | 16 | 17
  | 18 | 19 | 20 | 21 | 22 | 23 =>
    simp only [perm4Fn, vec4, pack4]; omega
  | _ + 24 => omega

private theorem perm4_comp : ∀ a b : Fin 24, ∃ c : Fin 24, ∀ i : Fin 4, perm4Fn a (perm4Fn b i) = perm4Fn c i := by
  decide
private theorem perm4_inv : ∀ a : Fin 24, ∃ b : Fin 24, (∀ i : Fin 4, perm4Fn a (perm4Fn b i) = i) ∧ (∀ i : Fin 4, perm4Fn b (perm4Fn a i) = i) := by
  decide
private theorem perm3_comp : ∀ a b : Fin 6, ∃ c : Fin 6, ∀ i : Fin 3, perm3Fn a (perm3Fn b i) = perm3Fn c i := by
  decide
private theorem perm3_inv : ∀ a : Fin 6, ∃ b : Fin 6, (∀ i : Fin 3, perm3Fn a (perm3Fn b i) = i) ∧ (∀ i : Fin 3, perm3Fn b (perm3Fn a i) = i) := by
  decide

private def IsPerm4 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) : Prop :=
  ∃ pi : Fin 24,
    let f := vec4 a0 a1 a2 a3
    b0 = f (perm4Fn pi ⟨0, by decide⟩) ∧ b1 = f (perm4Fn pi ⟨1, by decide⟩) ∧
    b2 = f (perm4Fn pi ⟨2, by decide⟩) ∧ b3 = f (perm4Fn pi ⟨3, by decide⟩)

private theorem isPerm4_trans {a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 : Nat}
    (h1 : IsPerm4 a0 a1 a2 a3 b0 b1 b2 b3) (h2 : IsPerm4 b0 b1 b2 b3 c0 c1 c2 c3) :
    IsPerm4 a0 a1 a2 a3 c0 c1 c2 c3 := by
  rcases h1 with ⟨p1, hb0, hb1, hb2, hb3⟩
  rcases h2 with ⟨p2, hc0, hc1, hc2, hc3⟩
  obtain ⟨p3, hp3⟩ := perm4_comp p1 p2
  have hvec : ∀ j : Fin 4, vec4 b0 b1 b2 b3 j = vec4 a0 a1 a2 a3 (perm4Fn p1 j) := by
    intro j; match j with
    | ⟨0, _⟩ => exact hb0 | ⟨1, _⟩ => exact hb1 | ⟨2, _⟩ => exact hb2 | ⟨3, _⟩ => exact hb3
  exact ⟨p3, by rw [hc0, hvec, hp3], by rw [hc1, hvec, hp3], by rw [hc2, hvec, hp3], by rw [hc3, hvec, hp3]⟩

private theorem sort4Tuple_spec (a0 a1 a2 a3 : Nat) :
    ((sort4Tuple a0 a1 a2 a3).1 ≤ (sort4Tuple a0 a1 a2 a3).2.1 ∧
     (sort4Tuple a0 a1 a2 a3).2.1 ≤ (sort4Tuple a0 a1 a2 a3).2.2.1 ∧
     (sort4Tuple a0 a1 a2 a3).2.2.1 ≤ (sort4Tuple a0 a1 a2 a3).2.2.2) ∧
    (∃ pi : Fin 24,
      let f := vec4 a0 a1 a2 a3
      (sort4Tuple a0 a1 a2 a3).1 = f (perm4Fn pi ⟨0, by decide⟩) ∧
      (sort4Tuple a0 a1 a2 a3).2.1 = f (perm4Fn pi ⟨1, by decide⟩) ∧
      (sort4Tuple a0 a1 a2 a3).2.2.1 = f (perm4Fn pi ⟨2, by decide⟩) ∧
      (sort4Tuple a0 a1 a2 a3).2.2.2 = f (perm4Fn pi ⟨3, by decide⟩)) := by
  constructor
  · let P : Nat × Nat × Nat × Nat → Prop := fun t =>
      t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2.1 ∧ t.2.2.1 ≤ t.2.2.2
    change P (sort4Tuple a0 a1 a2 a3)
    unfold sort4Tuple
    apply cmpSwap_cases <;> intro _
    all_goals (apply cmpSwap_cases <;> intro _)
    all_goals (apply cmpSwap_cases <;> intro _)
    all_goals (apply cmpSwap_cases <;> intro _)
    all_goals (apply cmpSwap_cases <;> intro _)
    all_goals (dsimp only [P]; omega)
  · change IsPerm4 a0 a1 a2 a3 (sort4Tuple a0 a1 a2 a3).1 (sort4Tuple a0 a1 a2 a3).2.1
      (sort4Tuple a0 a1 a2 a3).2.2.1 (sort4Tuple a0 a1 a2 a3).2.2.2
    let step1 (x : Nat × Nat × Nat × Nat) := cmpSwap x.1 x.2.1 fun b0 b1 => (b0, b1, x.2.2.1, x.2.2.2)
    let step2 (x : Nat × Nat × Nat × Nat) := cmpSwap x.2.2.1 x.2.2.2 fun b2 b3 => (x.1, x.2.1, b2, b3)
    let step3 (x : Nat × Nat × Nat × Nat) := cmpSwap x.1 x.2.2.1 fun c0 c2 => (c0, x.2.1, c2, x.2.2.2)
    let step4 (x : Nat × Nat × Nat × Nat) := cmpSwap x.2.1 x.2.2.2 fun c1 c3 => (x.1, c1, x.2.2.1, c3)
    let step5 (x : Nat × Nat × Nat × Nat) := cmpSwap x.2.1 x.2.2.1 fun d1 d2 => (x.1, d1, d2, x.2.2.2)
    have h1 : ∀ x : Nat × Nat × Nat × Nat, IsPerm4 x.1 x.2.1 x.2.2.1 x.2.2.2
        (step1 x).1 (step1 x).2.1 (step1 x).2.2.1 (step1 x).2.2.2 := by
      intro ⟨x0, x1, x2, x3⟩; dsimp only [step1]; unfold cmpSwap; split
      · exact ⟨⟨0, by decide⟩, rfl, rfl, rfl, rfl⟩
      · exact ⟨⟨6, by decide⟩, rfl, rfl, rfl, rfl⟩
    have h2 : ∀ x : Nat × Nat × Nat × Nat, IsPerm4 x.1 x.2.1 x.2.2.1 x.2.2.2
        (step2 x).1 (step2 x).2.1 (step2 x).2.2.1 (step2 x).2.2.2 := by
      intro ⟨x0, x1, x2, x3⟩; dsimp only [step2]; unfold cmpSwap; split
      · exact ⟨⟨0, by decide⟩, rfl, rfl, rfl, rfl⟩
      · exact ⟨⟨1, by decide⟩, rfl, rfl, rfl, rfl⟩
    have h3 : ∀ x : Nat × Nat × Nat × Nat, IsPerm4 x.1 x.2.1 x.2.2.1 x.2.2.2
        (step3 x).1 (step3 x).2.1 (step3 x).2.2.1 (step3 x).2.2.2 := by
      intro ⟨x0, x1, x2, x3⟩; dsimp only [step3]; unfold cmpSwap; split
      · exact ⟨⟨0, by decide⟩, rfl, rfl, rfl, rfl⟩
      · exact ⟨⟨14, by decide⟩, rfl, rfl, rfl, rfl⟩
    have h4 : ∀ x : Nat × Nat × Nat × Nat, IsPerm4 x.1 x.2.1 x.2.2.1 x.2.2.2
        (step4 x).1 (step4 x).2.1 (step4 x).2.2.1 (step4 x).2.2.2 := by
      intro ⟨x0, x1, x2, x3⟩; dsimp only [step4]; unfold cmpSwap; split
      · exact ⟨⟨0, by decide⟩, rfl, rfl, rfl, rfl⟩
      · exact ⟨⟨5, by decide⟩, rfl, rfl, rfl, rfl⟩
    have h5 : ∀ x : Nat × Nat × Nat × Nat, IsPerm4 x.1 x.2.1 x.2.2.1 x.2.2.2
        (step5 x).1 (step5 x).2.1 (step5 x).2.2.1 (step5 x).2.2.2 := by
      intro ⟨x0, x1, x2, x3⟩; dsimp only [step5]; unfold cmpSwap; split
      · exact ⟨⟨0, by decide⟩, rfl, rfl, rfl, rfl⟩
      · exact ⟨⟨2, by decide⟩, rfl, rfl, rfl, rfl⟩
    have hcomp : sort4Tuple a0 a1 a2 a3 = step5 (step4 (step3 (step2 (step1 (a0, a1, a2, a3))))) := by
      unfold sort4Tuple
      dsimp only [step1]
      simp only [cmpSwap_map step2]; dsimp only [step2]
      simp only [cmpSwap_map step3]; dsimp only [step3]
      simp only [cmpSwap_map step4]; dsimp only [step4]
      simp only [cmpSwap_map step5]; dsimp only [step5]
    rw [hcomp]
    exact isPerm4_trans (h1 _) (isPerm4_trans (h2 _) (isPerm4_trans (h3 _) (isPerm4_trans (h4 _) (h5 _))))

private theorem vec4_eta {α : Type} (f : Fin 4 → α) :
    vec4 (f ⟨0, by decide⟩) (f ⟨1, by decide⟩) (f ⟨2, by decide⟩) (f ⟨3, by decide⟩) = f := by
  funext i; match i with | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => rfl

private theorem sort4Pack_le_perm (f : Fin 4 → Nat) (pi : Fin 24) :
    sort4Pack (f ⟨0, by decide⟩) (f ⟨1, by decide⟩) (f ⟨2, by decide⟩) (f ⟨3, by decide⟩) ≤
      pack4 (f (perm4Fn pi ⟨0, by decide⟩)) (f (perm4Fn pi ⟨1, by decide⟩))
            (f (perm4Fn pi ⟨2, by decide⟩)) (f (perm4Fn pi ⟨3, by decide⟩)) := by
  have hspec := sort4Tuple_spec (f ⟨0, by decide⟩) (f ⟨1, by decide⟩) (f ⟨2, by decide⟩) (f ⟨3, by decide⟩)
  rcases hspec with ⟨hsorted, ⟨p0, hp0, hp1, hp2, hp3⟩⟩
  rw [vec4_eta] at hp0 hp1 hp2 hp3
  obtain ⟨p0inv, hinvL, _⟩ := perm4_inv p0
  obtain ⟨q, hq⟩ := perm4_comp p0inv pi
  have hidx : ∀ j : Fin 4,
      vec4 (sort4Tuple (f ⟨0, by decide⟩) (f ⟨1, by decide⟩) (f ⟨2, by decide⟩) (f ⟨3, by decide⟩)).1
           (sort4Tuple (f ⟨0, by decide⟩) (f ⟨1, by decide⟩) (f ⟨2, by decide⟩) (f ⟨3, by decide⟩)).2.1
           (sort4Tuple (f ⟨0, by decide⟩) (f ⟨1, by decide⟩) (f ⟨2, by decide⟩) (f ⟨3, by decide⟩)).2.2.1
           (sort4Tuple (f ⟨0, by decide⟩) (f ⟨1, by decide⟩) (f ⟨2, by decide⟩) (f ⟨3, by decide⟩)).2.2.2 j =
      f (perm4Fn p0 j) := by
    intro j; match j with
    | ⟨0, _⟩ => exact hp0
    | ⟨1, _⟩ => exact hp1
    | ⟨2, _⟩ => exact hp2
    | ⟨3, _⟩ => exact hp3
  have hle := pack4_le_of_sorted hsorted q
  rw [sort4Pack_eq]
  simp only [← hq, hidx, hinvL] at hle
  exact hle

private theorem min_eq_or (a b : Nat) : Nat.min a b = a ∨ Nat.min a b = b := by
  simp only [Nat.min_def]; split <;> simp

private theorem min6_eq (a0 a1 a2 a3 a4 a5 : Nat) :
    let m := Nat.min a0 (Nat.min a1 (Nat.min a2 (Nat.min a3 (Nat.min a4 a5))))
    m = a0 ∨ m = a1 ∨ m = a2 ∨ m = a3 ∨ m = a4 ∨ m = a5 := by
  dsimp only
  rcases min_eq_or a0 _ with h | h; · exact Or.inl h
  rw [h]; rcases min_eq_or a1 _ with h | h; · exact Or.inr (Or.inl h)
  rw [h]; rcases min_eq_or a2 _ with h | h; · exact Or.inr (Or.inr (Or.inl h))
  rw [h]; rcases min_eq_or a3 _ with h | h; · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  rw [h]; rcases min_eq_or a4 a5 with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

private theorem canon_le_perm {g : Grid} (hg : validGrid g) (pi : Fin 24) (si : Fin 6) :
    canon g ≤ packGrid (permGrid pi si g) := by
  have hcol0 : ∀ p, permRow (rowCode (g p)) 0 1 2 = rowCode (fun h => g p (perm3Fn ⟨0, by decide⟩ h)) :=
    fun p => permRow_eq (hg p) ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩
  have hcol1 : ∀ p, permRow (rowCode (g p)) 0 2 1 = rowCode (fun h => g p (perm3Fn ⟨1, by decide⟩ h)) :=
    fun p => permRow_eq (hg p) ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨1, by decide⟩
  have hcol2 : ∀ p, permRow (rowCode (g p)) 1 0 2 = rowCode (fun h => g p (perm3Fn ⟨2, by decide⟩ h)) :=
    fun p => permRow_eq (hg p) ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨2, by decide⟩
  have hcol3 : ∀ p, permRow (rowCode (g p)) 1 2 0 = rowCode (fun h => g p (perm3Fn ⟨3, by decide⟩ h)) :=
    fun p => permRow_eq (hg p) ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨0, by decide⟩
  have hcol4 : ∀ p, permRow (rowCode (g p)) 2 0 1 = rowCode (fun h => g p (perm3Fn ⟨4, by decide⟩ h)) :=
    fun p => permRow_eq (hg p) ⟨2, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩
  have hcol5 : ∀ p, permRow (rowCode (g p)) 2 1 0 = rowCode (fun h => g p (perm3Fn ⟨5, by decide⟩ h)) :=
    fun p => permRow_eq (hg p) ⟨2, by decide⟩ ⟨1, by decide⟩ ⟨0, by decide⟩
  have hs_le : ∀ s : Fin 6,
      canon g ≤ sort4Pack (rowCode (fun h => g ⟨0, by decide⟩ (perm3Fn s h)))
                          (rowCode (fun h => g ⟨1, by decide⟩ (perm3Fn s h)))
                          (rowCode (fun h => g ⟨2, by decide⟩ (perm3Fn s h)))
                          (rowCode (fun h => g ⟨3, by decide⟩ (perm3Fn s h))) := by
    intro s
    unfold canon canonRows
    match s with
    | ⟨0, _⟩ =>
      rw [hcol0, hcol0, hcol0, hcol0]; exact Nat.min_le_left _ _
    | ⟨1, _⟩ =>
      rw [hcol1, hcol1, hcol1, hcol1]
      exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
    | ⟨2, _⟩ =>
      rw [hcol2, hcol2, hcol2, hcol2]
      exact Nat.le_trans (Nat.min_le_right _ _) (Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _))
    | ⟨3, _⟩ =>
      rw [hcol3, hcol3, hcol3, hcol3]
      exact Nat.le_trans (Nat.min_le_right _ _) (Nat.le_trans (Nat.min_le_right _ _)
        (Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)))
    | ⟨4, _⟩ =>
      rw [hcol4, hcol4, hcol4, hcol4]
      exact Nat.le_trans (Nat.min_le_right _ _) (Nat.le_trans (Nat.min_le_right _ _)
        (Nat.le_trans (Nat.min_le_right _ _) (Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _))))
    | ⟨5, _⟩ =>
      rw [hcol5, hcol5, hcol5, hcol5]
      exact Nat.le_trans (Nat.min_le_right _ _) (Nat.le_trans (Nat.min_le_right _ _)
        (Nat.le_trans (Nat.min_le_right _ _) (Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _))))
  have hle1 := hs_le si
  have hle2 := sort4Pack_le_perm (fun p => rowCode (fun h => g p (perm3Fn si h))) pi
  exact Nat.le_trans hle1 hle2

private theorem canon_exists_perm {g : Grid} (hg : validGrid g) :
    ∃ (pi : Fin 24) (si : Fin 6),
      let c := permGrid pi si g
      packGrid c = canon g ∧
      rowCode (c ⟨0, by decide⟩) ≤ rowCode (c ⟨1, by decide⟩) ∧
      rowCode (c ⟨1, by decide⟩) ≤ rowCode (c ⟨2, by decide⟩) ∧
      rowCode (c ⟨2, by decide⟩) ≤ rowCode (c ⟨3, by decide⟩) := by
  have hcol0 : ∀ p, permRow (rowCode (g p)) 0 1 2 = rowCode (fun h => g p (perm3Fn ⟨0, by decide⟩ h)) :=
    fun p => permRow_eq (hg p) ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩
  have hcol1 : ∀ p, permRow (rowCode (g p)) 0 2 1 = rowCode (fun h => g p (perm3Fn ⟨1, by decide⟩ h)) :=
    fun p => permRow_eq (hg p) ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨1, by decide⟩
  have hcol2 : ∀ p, permRow (rowCode (g p)) 1 0 2 = rowCode (fun h => g p (perm3Fn ⟨2, by decide⟩ h)) :=
    fun p => permRow_eq (hg p) ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨2, by decide⟩
  have hcol3 : ∀ p, permRow (rowCode (g p)) 1 2 0 = rowCode (fun h => g p (perm3Fn ⟨3, by decide⟩ h)) :=
    fun p => permRow_eq (hg p) ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨0, by decide⟩
  have hcol4 : ∀ p, permRow (rowCode (g p)) 2 0 1 = rowCode (fun h => g p (perm3Fn ⟨4, by decide⟩ h)) :=
    fun p => permRow_eq (hg p) ⟨2, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩
  have hcol5 : ∀ p, permRow (rowCode (g p)) 2 1 0 = rowCode (fun h => g p (perm3Fn ⟨5, by decide⟩ h)) :=
    fun p => permRow_eq (hg p) ⟨2, by decide⟩ ⟨1, by decide⟩ ⟨0, by decide⟩
  have hex_s : ∃ si : Fin 6,
      canon g = sort4Pack (rowCode (fun h => g ⟨0, by decide⟩ (perm3Fn si h)))
                          (rowCode (fun h => g ⟨1, by decide⟩ (perm3Fn si h)))
                          (rowCode (fun h => g ⟨2, by decide⟩ (perm3Fn si h)))
                          (rowCode (fun h => g ⟨3, by decide⟩ (perm3Fn si h))) := by
    unfold canon canonRows
    rcases min6_eq
      (sort4Pack (permRow (rowCode (g ⟨0, by decide⟩)) 0 1 2) (permRow (rowCode (g ⟨1, by decide⟩)) 0 1 2)
                 (permRow (rowCode (g ⟨2, by decide⟩)) 0 1 2) (permRow (rowCode (g ⟨3, by decide⟩)) 0 1 2))
      (sort4Pack (permRow (rowCode (g ⟨0, by decide⟩)) 0 2 1) (permRow (rowCode (g ⟨1, by decide⟩)) 0 2 1)
                 (permRow (rowCode (g ⟨2, by decide⟩)) 0 2 1) (permRow (rowCode (g ⟨3, by decide⟩)) 0 2 1))
      (sort4Pack (permRow (rowCode (g ⟨0, by decide⟩)) 1 0 2) (permRow (rowCode (g ⟨1, by decide⟩)) 1 0 2)
                 (permRow (rowCode (g ⟨2, by decide⟩)) 1 0 2) (permRow (rowCode (g ⟨3, by decide⟩)) 1 0 2))
      (sort4Pack (permRow (rowCode (g ⟨0, by decide⟩)) 1 2 0) (permRow (rowCode (g ⟨1, by decide⟩)) 1 2 0)
                 (permRow (rowCode (g ⟨2, by decide⟩)) 1 2 0) (permRow (rowCode (g ⟨3, by decide⟩)) 1 2 0))
      (sort4Pack (permRow (rowCode (g ⟨0, by decide⟩)) 2 0 1) (permRow (rowCode (g ⟨1, by decide⟩)) 2 0 1)
                 (permRow (rowCode (g ⟨2, by decide⟩)) 2 0 1) (permRow (rowCode (g ⟨3, by decide⟩)) 2 0 1))
      (sort4Pack (permRow (rowCode (g ⟨0, by decide⟩)) 2 1 0) (permRow (rowCode (g ⟨1, by decide⟩)) 2 1 0)
                 (permRow (rowCode (g ⟨2, by decide⟩)) 2 1 0) (permRow (rowCode (g ⟨3, by decide⟩)) 2 1 0))
      with h | h | h | h | h | h
    · exact ⟨⟨0, by decide⟩, by rw [← hcol0, ← hcol0, ← hcol0, ← hcol0]; exact h⟩
    · exact ⟨⟨1, by decide⟩, by rw [← hcol1, ← hcol1, ← hcol1, ← hcol1]; exact h⟩
    · exact ⟨⟨2, by decide⟩, by rw [← hcol2, ← hcol2, ← hcol2, ← hcol2]; exact h⟩
    · exact ⟨⟨3, by decide⟩, by rw [← hcol3, ← hcol3, ← hcol3, ← hcol3]; exact h⟩
    · exact ⟨⟨4, by decide⟩, by rw [← hcol4, ← hcol4, ← hcol4, ← hcol4]; exact h⟩
    · exact ⟨⟨5, by decide⟩, by rw [← hcol5, ← hcol5, ← hcol5, ← hcol5]; exact h⟩
  rcases hex_s with ⟨si, hsi⟩
  let f : Fin 4 → Nat := fun p => rowCode (fun h => g p (perm3Fn si h))
  have hspec := sort4Tuple_spec (f ⟨0, by decide⟩) (f ⟨1, by decide⟩) (f ⟨2, by decide⟩) (f ⟨3, by decide⟩)
  rcases hspec with ⟨⟨hs1, hs2, hs3⟩, ⟨pi, hp0, hp1, hp2, hp3⟩⟩
  rw [vec4_eta] at hp0 hp1 hp2 hp3
  refine ⟨pi, si, ?_, ?_, ?_, ?_⟩
  · change pack4 (f (perm4Fn pi ⟨0, by decide⟩)) (f (perm4Fn pi ⟨1, by decide⟩))
                 (f (perm4Fn pi ⟨2, by decide⟩)) (f (perm4Fn pi ⟨3, by decide⟩)) = canon g
    rw [hsi, sort4Pack_eq, hp0, hp1, hp2, hp3]
  · change f (perm4Fn pi ⟨0, by decide⟩) ≤ f (perm4Fn pi ⟨1, by decide⟩); rw [← hp0, ← hp1]; exact hs1
  · change f (perm4Fn pi ⟨1, by decide⟩) ≤ f (perm4Fn pi ⟨2, by decide⟩); rw [← hp1, ← hp2]; exact hs2
  · change f (perm4Fn pi ⟨2, by decide⟩) ≤ f (perm4Fn pi ⟨3, by decide⟩); rw [← hp2, ← hp3]; exact hs3

private theorem validGrid_perm {g : Grid} (hg : validGrid g) (pi : Fin 24) (si : Fin 6) :
    validGrid (permGrid pi si g) := fun _ _ => hg _ _

private theorem canon_perm {g : Grid} (hg : validGrid g) (pi : Fin 24) (si : Fin 6) :
    canon (permGrid pi si g) = canon g := by
  apply Nat.le_antisymm
  · obtain ⟨p0, s0, h0, _⟩ := canon_exists_perm hg
    obtain ⟨pinv, hpinv, _⟩ := perm4_inv pi
    obtain ⟨sinv, hsinv, _⟩ := perm3_inv si
    obtain ⟨p1, hp1⟩ := perm4_comp pinv p0
    obtain ⟨s1, hs1⟩ := perm3_comp sinv s0
    have heq : permGrid p1 s1 (permGrid pi si g) = permGrid p0 s0 g := by
      funext p h; simp only [permGrid, ← hp1, ← hs1, hpinv, hsinv]
    rw [← h0, ← heq]
    exact canon_le_perm (validGrid_perm hg pi si) p1 s1
  · obtain ⟨p0, s0, h0, _⟩ := canon_exists_perm (validGrid_perm hg pi si)
    obtain ⟨p1, hp1⟩ := perm4_comp pi p0
    obtain ⟨s1, hs1⟩ := perm3_comp si s0
    have heq : permGrid p1 s1 g = permGrid p0 s0 (permGrid pi si g) := by
      funext p h; simp only [permGrid, ← hp1, ← hs1]
    rw [← h0, ← heq]
    exact canon_le_perm hg p1 s1

private def SemFalsified (g : Grid) : Prop :=
  (∃ p : Fin 4, ∀ h : Fin 3, g p h = 1) ∨
  (∃ h : Fin 3, ∃ p1 p2 : Fin 4, p1 ≠ p2 ∧ g p1 h = 2 ∧ g p2 h = 2)

private theorem rowCode_eq_13 {r : Fin 3 → Nat} (hr : ∀ h, r h < 3) :
    (rowCode r == 13) = true ↔ ∀ h : Fin 3, r h = 1 := by
  have h0 := hr ⟨0, by decide⟩; have h1 := hr ⟨1, by decide⟩; have h2 := hr ⟨2, by decide⟩
  unfold rowCode; simp only [beq_iff_eq]
  constructor
  · intro heq h; match h with | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ => omega
  · intro hall
    have := hall ⟨0, by decide⟩; have := hall ⟨1, by decide⟩; have := hall ⟨2, by decide⟩; omega

private theorem rowTwos_bit {r : Fin 3 → Nat} (hr : ∀ h, r h < 3) (h : Fin 3) :
    ((rowTwos (rowCode r)).testBit h.val = true) ↔ r h = 2 := by
  have c0 := hr ⟨0, by decide⟩; have c1 := hr ⟨1, by decide⟩; have c2 := hr ⟨2, by decide⟩
  have e0 : rowCode r % 3 = r ⟨0, by decide⟩ := by unfold rowCode; omega
  have e1 : (rowCode r / 3) % 3 = r ⟨1, by decide⟩ := by unfold rowCode; omega
  have e2 : rowCode r / 9 = r ⟨2, by decide⟩ := by unfold rowCode; omega
  have hdec : ∀ (a0 a1 a2 : Fin 3) (hi : Fin 3),
      (((if a0.val == 2 then 1 else 0) + (if a1.val == 2 then 2 else 0) + (if a2.val == 2 then 4 else 0)).testBit hi.val = true) ↔
      (vec3 a0.val a1.val a2.val hi = 2) := by
    decide +kernel
  unfold rowTwos; rw [e0, e1, e2]
  have hv : vec3 (r ⟨0, by decide⟩) (r ⟨1, by decide⟩) (r ⟨2, by decide⟩) h = r h := by
    match h with | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ => rfl
  rw [← hv]
  exact hdec ⟨r ⟨0, by decide⟩, c0⟩ ⟨r ⟨1, by decide⟩, c1⟩ ⟨r ⟨2, by decide⟩, c2⟩ h

private theorem mask_overlap_iff {m0 m1 m2 m3 : Nat}
    (hm0 : m0 < 8) (hm1 : m1 < 8) (hm2 : m2 < 8) (hm3 : m3 < 8) :
    hasColClash m0 m1 m2 m3 = true ↔
    ∃ h : Fin 3, ∃ p1 p2 : Fin 4, p1 ≠ p2 ∧
      (vec4 m0 m1 m2 m3 p1).testBit h.val = true ∧
      (vec4 m0 m1 m2 m3 p2).testBit h.val = true := by
  have hdec : ∀ a0 a1 a2 a3 : Fin 8,
      (hasColClash a0.val a1.val a2.val a3.val = true) ↔
      ∃ h : Fin 3, ∃ p1 p2 : Fin 4, p1 ≠ p2 ∧
        (vec4 a0.val a1.val a2.val a3.val p1).testBit h.val = true ∧
        (vec4 a0.val a1.val a2.val a3.val p2).testBit h.val = true := by
    decide +kernel
  exact hdec ⟨m0, hm0⟩ ⟨m1, hm1⟩ ⟨m2, hm2⟩ ⟨m3, hm3⟩

private theorem rowTwos_lt (r : Nat) : rowTwos r < 8 := by
  unfold rowTwos; split <;> split <;> split <;> omega

private theorem isFalsified_iff {g : Grid} (hg : validGrid g) :
    isFalsified g = true ↔ SemFalsified g := by
  unfold isFalsified isFalsifiedRows SemFalsified
  simp only [Bool.or_eq_true, rowCode_eq_13 (hg ⟨0, by decide⟩), rowCode_eq_13 (hg ⟨1, by decide⟩),
    rowCode_eq_13 (hg ⟨2, by decide⟩), rowCode_eq_13 (hg ⟨3, by decide⟩)]
  rw [mask_overlap_iff (rowTwos_lt _) (rowTwos_lt _) (rowTwos_lt _) (rowTwos_lt _)]
  have hidx : ∀ p : Fin 4,
      vec4 (rowTwos (rowCode (g ⟨0, by decide⟩))) (rowTwos (rowCode (g ⟨1, by decide⟩)))
           (rowTwos (rowCode (g ⟨2, by decide⟩))) (rowTwos (rowCode (g ⟨3, by decide⟩))) p =
      rowTwos (rowCode (g p)) := fun p => by match p with | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => rfl
  simp only [hidx, rowTwos_bit (hg _)]
  constructor
  · rintro ((((h0 | h1) | h2) | h3) | hc)
    · exact Or.inl ⟨⟨0, by decide⟩, h0⟩
    · exact Or.inl ⟨⟨1, by decide⟩, h1⟩
    · exact Or.inl ⟨⟨2, by decide⟩, h2⟩
    · exact Or.inl ⟨⟨3, by decide⟩, h3⟩
    · exact Or.inr hc
  · rintro (⟨p, hp⟩ | hc)
    · match p with
      | ⟨0, _⟩ => exact Or.inl (Or.inl (Or.inl (Or.inl hp)))
      | ⟨1, _⟩ => exact Or.inl (Or.inl (Or.inl (Or.inr hp)))
      | ⟨2, _⟩ => exact Or.inl (Or.inl (Or.inr hp))
      | ⟨3, _⟩ => exact Or.inl (Or.inr hp)
    · exact Or.inr hc

private theorem isFalsified_perm {g : Grid} (hg : validGrid g) (pi : Fin 24) (si : Fin 6) :
    isFalsified (permGrid pi si g) = isFalsified g := by
  apply Bool.eq_iff_iff.mpr
  rw [isFalsified_iff (validGrid_perm hg pi si), isFalsified_iff hg]
  obtain ⟨pinv, hpinvL, hpinvR⟩ := perm4_inv pi
  obtain ⟨sinv, hsinvL, hsinvR⟩ := perm3_inv si
  unfold SemFalsified permGrid
  constructor
  · rintro (⟨p, hp⟩ | ⟨h, p1, p2, hne, h1, h2⟩)
    · refine Or.inl ⟨perm4Fn pi p, fun h => ?_⟩
      simpa [hsinvL] using hp (perm3Fn sinv h)
    · refine Or.inr ⟨perm3Fn si h, perm4Fn pi p1, perm4Fn pi p2, ?_, h1, h2⟩
      intro heq; apply hne
      have := congrArg (perm4Fn pinv) heq
      simpa [hpinvR] using this
  · rintro (⟨p, hp⟩ | ⟨h, p1, p2, hne, h1, h2⟩)
    · refine Or.inl ⟨perm4Fn pinv p, fun h => ?_⟩
      simpa [hpinvL] using hp (perm3Fn si h)
    · refine Or.inr ⟨perm3Fn sinv h, perm4Fn pinv p1, perm4Fn pinv p2, ?_,
        by simpa [hpinvL, hsinvL] using h1, by simpa [hpinvL, hsinvL] using h2⟩
      intro heq; apply hne
      have := congrArg (perm4Fn pi) heq
      simpa [hpinvL] using this

private theorem lb_perm {g : Grid} (hg : validGrid g) (pi : Fin 24) (si : Fin 6) :
    lb (permGrid pi si g) = lb g := by
  unfold lb lbRows
  change (if isFalsified (permGrid pi si g) then 1 else dpBST.find (canon (permGrid pi si g))) =
         (if isFalsified g then 1 else dpBST.find (canon g))
  rw [isFalsified_perm hg pi si, canon_perm hg pi si]

/-! ## 4. Exhaustive kernel check on the 814 canonical orbits -/

private def setRowCell (r h val : Nat) : Nat :=
  let c0 := if h == 0 then val else r % 3
  let c1 := if h == 1 then val else (r / 3) % 3
  let c2 := if h == 2 then val else r / 9
  c0 + 3 * c1 + 9 * c2

private def getRowCell (r h : Nat) : Nat :=
  if h == 0 then r % 3 else if h == 1 then (r / 3) % 3 else r / 9

private def checkRow (v r0 r1 r2 r3 p h : Nat) : Bool :=
  let rp := if p == 0 then r0 else if p == 1 then r1 else if p == 2 then r2 else r3
  if getRowCell rp h != 0 then true
  else
    let r1' := setRowCell rp h 1
    let r2' := setRowCell rp h 2
    let v1 := match p with
      | 0 => lbRows r1' r1 r2 r3
      | 1 => lbRows r0 r1' r2 r3
      | 2 => lbRows r0 r1 r1' r3
      | _ => lbRows r0 r1 r2 r1'
    let v2 := match p with
      | 0 => lbRows r2' r1 r2 r3
      | 1 => lbRows r0 r2' r2 r3
      | 2 => lbRows r0 r1 r2' r3
      | _ => lbRows r0 r1 r2 r2'
    Nat.ble v (v1 + v2)

private def checkOrbit (r0 r1 r2 r3 : Nat) : Bool :=
  if canonRows r0 r1 r2 r3 != pack4 r0 r1 r2 r3 then true
  else
    let v := dpBST.find (pack4 r0 r1 r2 r3)
    checkRow v r0 r1 r2 r3 0 0 && checkRow v r0 r1 r2 r3 0 1 && checkRow v r0 r1 r2 r3 0 2 &&
    checkRow v r0 r1 r2 r3 1 0 && checkRow v r0 r1 r2 r3 1 1 && checkRow v r0 r1 r2 r3 1 2 &&
    checkRow v r0 r1 r2 r3 2 0 && checkRow v r0 r1 r2 r3 2 1 && checkRow v r0 r1 r2 r3 2 2 &&
    checkRow v r0 r1 r2 r3 3 0 && checkRow v r0 r1 r2 r3 3 1 && checkRow v r0 r1 r2 r3 3 2

private def checkR3 (r0 r1 r2 m012 : Nat) : Nat → Bool
  | 0 => true
  | k + 1 =>
    let r3 := 26 - k
    (if r3 < r2 || r3 == 13 || ((m012 &&& rowTwos r3) != 0) then true
     else checkOrbit r0 r1 r2 r3) && checkR3 r0 r1 r2 m012 k

private def checkR2 (r0 r1 m01 : Nat) : Nat → Bool
  | 0 => true
  | k + 1 =>
    let r2 := 26 - k
    (if r2 < r1 || r2 == 13 || ((m01 &&& rowTwos r2) != 0) then true
     else checkR3 r0 r1 r2 (m01 ||| rowTwos r2) 27) && checkR2 r0 r1 m01 k

private def checkR1 (r0 m0 : Nat) : Nat → Bool
  | 0 => true
  | k + 1 =>
    let r1 := 26 - k
    (if r1 < r0 || r1 == 13 || ((m0 &&& rowTwos r1) != 0) then true
     else checkR2 r0 r1 (m0 ||| rowTwos r1) 27) && checkR1 r0 m0 k

private def checkR0 : Nat → Bool
  | 0 => true
  | k + 1 =>
    let r0 := 26 - k
    (if r0 == 13 then true else checkR1 r0 (rowTwos r0) 27) && checkR0 k

private theorem checkAll_true : checkR0 27 = true := by decide +kernel

private theorem checkR3_sound {r0 r1 r2 m012 k r3 : Nat}
    (hk : checkR3 r0 r1 r2 m012 k = true)
    (hr : 27 - k ≤ r3 ∧ r3 < 27)
    (hge : r2 ≤ r3) (h13 : r3 ≠ 13) (hm : (m012 &&& rowTwos r3) = 0) :
    checkOrbit r0 r1 r2 r3 = true := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [checkR3, Bool.and_eq_true] at hk
    by_cases heq : r3 = 26 - k
    · subst heq
      have hcond : (26 - k < r2 || 26 - k == 13 || ((m012 &&& rowTwos (26 - k)) != 0)) = false := by
        simp [Nat.not_lt.mpr hge, h13, hm]
      simpa [hcond] using hk.1
    · exact ih hk.2 (by omega)

private theorem checkR2_sound {r0 r1 m01 k r2 r3 : Nat}
    (hk : checkR2 r0 r1 m01 k = true)
    (hr2 : 27 - k ≤ r2 ∧ r2 < 27) (hr3 : r3 < 27)
    (h12 : r1 ≤ r2) (h23 : r2 ≤ r3) (h13_2 : r2 ≠ 13) (h13_3 : r3 ≠ 13)
    (hm2 : (m01 &&& rowTwos r2) = 0) (hm3 : ((m01 ||| rowTwos r2) &&& rowTwos r3) = 0) :
    checkOrbit r0 r1 r2 r3 = true := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [checkR2, Bool.and_eq_true] at hk
    by_cases heq : r2 = 26 - k
    · subst heq
      have hcond : (26 - k < r1 || 26 - k == 13 || ((m01 &&& rowTwos (26 - k)) != 0)) = false := by
        simp [Nat.not_lt.mpr h12, h13_2, hm2]
      have h3 := hk.1; simp only [hcond, Bool.false_eq_true, ↓reduceIte] at h3
      exact checkR3_sound h3 ⟨by omega, hr3⟩ h23 h13_3 hm3
    · exact ih hk.2 (by omega)

private theorem checkR1_sound {r0 m0 k r1 r2 r3 : Nat}
    (hk : checkR1 r0 m0 k = true)
    (hr1 : 27 - k ≤ r1 ∧ r1 < 27) (hr2 : r2 < 27) (hr3 : r3 < 27)
    (h01 : r0 ≤ r1) (h12 : r1 ≤ r2) (h23 : r2 ≤ r3)
    (h13_1 : r1 ≠ 13) (h13_2 : r2 ≠ 13) (h13_3 : r3 ≠ 13)
    (hm1 : (m0 &&& rowTwos r1) = 0)
    (hm2 : ((m0 ||| rowTwos r1) &&& rowTwos r2) = 0)
    (hm3 : ((m0 ||| rowTwos r1 ||| rowTwos r2) &&& rowTwos r3) = 0) :
    checkOrbit r0 r1 r2 r3 = true := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [checkR1, Bool.and_eq_true] at hk
    by_cases heq : r1 = 26 - k
    · subst heq
      have hcond : (26 - k < r0 || 26 - k == 13 || ((m0 &&& rowTwos (26 - k)) != 0)) = false := by
        simp [Nat.not_lt.mpr h01, h13_1, hm1]
      have h2 := hk.1; simp only [hcond, Bool.false_eq_true, ↓reduceIte] at h2
      exact checkR2_sound h2 ⟨by omega, hr2⟩ hr3 h12 h23 h13_2 h13_3 hm2 hm3
    · exact ih hk.2 (by omega)

private theorem checkR0_sound {k r0 r1 r2 r3 : Nat}
    (hk : checkR0 k = true)
    (hr0 : 27 - k ≤ r0 ∧ r0 < 27) (hr1 : r1 < 27) (hr2 : r2 < 27) (hr3 : r3 < 27)
    (h01 : r0 ≤ r1) (h12 : r1 ≤ r2) (h23 : r2 ≤ r3)
    (hf : isFalsifiedRows r0 r1 r2 r3 = false) :
    checkOrbit r0 r1 r2 r3 = true := by
  have hf' : r0 ≠ 13 ∧ r1 ≠ 13 ∧ r2 ≠ 13 ∧ r3 ≠ 13 ∧
      (rowTwos r0 &&& rowTwos r1) = 0 ∧
      ((rowTwos r0 ||| rowTwos r1) &&& rowTwos r2) = 0 ∧
      ((rowTwos r0 ||| rowTwos r1 ||| rowTwos r2) &&& rowTwos r3) = 0 := by
    unfold isFalsifiedRows hasColClash at hf
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq] at hf
    rcases hf with ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, ⟨⟨hm1, hm2⟩, hm3⟩⟩
    exact ⟨h0, h1, h2, h3, hm1, hm2, hm3⟩
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [checkR0, Bool.and_eq_true] at hk
    by_cases heq : r0 = 26 - k
    · subst heq
      have hcond : (26 - k == 13) = false := by simp [hf'.1]
      have h1 := hk.1; simp only [hcond, Bool.false_eq_true, ↓reduceIte] at h1
      exact checkR1_sound h1 ⟨by omega, hr1⟩ hr2 hr3 h01 h12 h23
        hf'.2.1 hf'.2.2.1 hf'.2.2.2.1 hf'.2.2.2.2.1 hf'.2.2.2.2.2.1 hf'.2.2.2.2.2.2
    · exact ih hk.2 (by omega)

private theorem rowCode_setCell {r : Fin 3 → Nat} (hr : ∀ h, r h < 3) (h : Fin 3) (val : Nat) :
    rowCode (fun h' => if h' = h then val else r h') = setRowCell (rowCode r) h.val val := by
  have c0 := hr ⟨0, by decide⟩; have c1 := hr ⟨1, by decide⟩; have c2 := hr ⟨2, by decide⟩
  have e0 : rowCode r % 3 = r ⟨0, by decide⟩ := by unfold rowCode; omega
  have e1 : (rowCode r / 3) % 3 = r ⟨1, by decide⟩ := by unfold rowCode; omega
  have e2 : rowCode r / 9 = r ⟨2, by decide⟩ := by unfold rowCode; omega
  unfold setRowCell; rw [e0, e1, e2]; unfold rowCode
  match h with | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ => rfl

private theorem getRowCell_eq {r : Fin 3 → Nat} (hr : ∀ h, r h < 3) (h : Fin 3) :
    getRowCell (rowCode r) h.val = r h := by
  have c0 := hr ⟨0, by decide⟩; have c1 := hr ⟨1, by decide⟩; have c2 := hr ⟨2, by decide⟩
  have e0 : rowCode r % 3 = r ⟨0, by decide⟩ := by unfold rowCode; omega
  have e1 : (rowCode r / 3) % 3 = r ⟨1, by decide⟩ := by unfold rowCode; omega
  have e2 : rowCode r / 9 = r ⟨2, by decide⟩ := by unfold rowCode; omega
  unfold getRowCell; rw [e0, e1, e2]
  match h with | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ => rfl

private theorem lb_step_canon {c : Grid} (hc : validGrid c)
    (hsorted : rowCode (c ⟨0, by decide⟩) ≤ rowCode (c ⟨1, by decide⟩) ∧
               rowCode (c ⟨1, by decide⟩) ≤ rowCode (c ⟨2, by decide⟩) ∧
               rowCode (c ⟨2, by decide⟩) ≤ rowCode (c ⟨3, by decide⟩))
    (hcanon : canon c = packGrid c)
    (hf : isFalsified c = false)
    (p : Fin 4) (h : Fin 3) (hz : c p h = 0) :
    lb c ≤ lb (setCell c p h 1) + lb (setCell c p h 2) := by
  have horb := checkR0_sound checkAll_true ⟨by omega, rowCode_lt (hc ⟨0, by decide⟩)⟩
    (rowCode_lt (hc ⟨1, by decide⟩)) (rowCode_lt (hc ⟨2, by decide⟩)) (rowCode_lt (hc ⟨3, by decide⟩))
    hsorted.1 hsorted.2.1 hsorted.2.2 hf
  unfold checkOrbit at horb
  have hcanon' : canonRows (rowCode (c ⟨0, by decide⟩)) (rowCode (c ⟨1, by decide⟩))
      (rowCode (c ⟨2, by decide⟩)) (rowCode (c ⟨3, by decide⟩)) =
      pack4 (rowCode (c ⟨0, by decide⟩)) (rowCode (c ⟨1, by decide⟩))
      (rowCode (c ⟨2, by decide⟩)) (rowCode (c ⟨3, by decide⟩)) := hcanon
  have hneq : (canonRows (rowCode (c ⟨0, by decide⟩)) (rowCode (c ⟨1, by decide⟩))
      (rowCode (c ⟨2, by decide⟩)) (rowCode (c ⟨3, by decide⟩)) !=
      pack4 (rowCode (c ⟨0, by decide⟩)) (rowCode (c ⟨1, by decide⟩))
      (rowCode (c ⟨2, by decide⟩)) (rowCode (c ⟨3, by decide⟩))) = false := by
    rw [hcanon']; exact bne_self_eq_false _
  simp only [hneq, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at horb
  have hcr : checkRow (dpBST.find (packGrid c))
      (rowCode (c ⟨0, by decide⟩)) (rowCode (c ⟨1, by decide⟩))
      (rowCode (c ⟨2, by decide⟩)) (rowCode (c ⟨3, by decide⟩)) p.val h.val = true := by
    match p, h with
    | ⟨0, _⟩, ⟨0, _⟩ => exact horb.1.1.1.1.1.1.1.1.1.1.1
    | ⟨0, _⟩, ⟨1, _⟩ => exact horb.1.1.1.1.1.1.1.1.1.1.2
    | ⟨0, _⟩, ⟨2, _⟩ => exact horb.1.1.1.1.1.1.1.1.1.2
    | ⟨1, _⟩, ⟨0, _⟩ => exact horb.1.1.1.1.1.1.1.1.2
    | ⟨1, _⟩, ⟨1, _⟩ => exact horb.1.1.1.1.1.1.1.2
    | ⟨1, _⟩, ⟨2, _⟩ => exact horb.1.1.1.1.1.1.2
    | ⟨2, _⟩, ⟨0, _⟩ => exact horb.1.1.1.1.1.2
    | ⟨2, _⟩, ⟨1, _⟩ => exact horb.1.1.1.1.2
    | ⟨2, _⟩, ⟨2, _⟩ => exact horb.1.1.1.2
    | ⟨3, _⟩, ⟨0, _⟩ => exact horb.1.1.2
    | ⟨3, _⟩, ⟨1, _⟩ => exact horb.1.2
    | ⟨3, _⟩, ⟨2, _⟩ => exact horb.2
  have hlb_c : lb c = dpBST.find (packGrid c) := by
    unfold lb lbRows
    change (if isFalsified c then 1 else dpBST.find (canon c)) = _
    rw [hf, hcanon]; rfl
  rw [hlb_c]
  have hsc1 : rowCode (setCell c p h 1 p) = setRowCell (rowCode (c p)) h.val 1 := by
    have : setCell c p h 1 p = fun h' => if h' = h then 1 else c p h' := by
      funext h'; simp [setCell]
    rw [this, rowCode_setCell (hc p)]
  have hsc2 : rowCode (setCell c p h 2 p) = setRowCell (rowCode (c p)) h.val 2 := by
    have : setCell c p h 2 p = fun h' => if h' = h then 2 else c p h' := by
      funext h'; simp [setCell]
    rw [this, rowCode_setCell (hc p)]
  have hsc_ne : ∀ (q : Fin 4) (v : Nat), q ≠ p → rowCode (setCell c p h v q) = rowCode (c q) := by
    intro q v hne; congr 1; funext h'; simp [setCell, hne]
  unfold checkRow at hcr
  match p with
  | ⟨0, _⟩ =>
    simp only [show (0 == 0) = true from rfl, ↓reduceIte, getRowCell_eq (hc ⟨0, by decide⟩), hz,
      bne_self_eq_false, Bool.false_eq_true, Nat.ble_eq] at hcr
    unfold lb
    rw [hsc1, hsc2,
        hsc_ne ⟨1, by decide⟩ 1 (fun h => by cases h), hsc_ne ⟨2, by decide⟩ 1 (fun h => by cases h), hsc_ne ⟨3, by decide⟩ 1 (fun h => by cases h),
        hsc_ne ⟨1, by decide⟩ 2 (fun h => by cases h), hsc_ne ⟨2, by decide⟩ 2 (fun h => by cases h), hsc_ne ⟨3, by decide⟩ 2 (fun h => by cases h)]
    exact hcr
  | ⟨1, _⟩ =>
    simp only [show (1 == 0) = false from rfl, show (1 == 1) = true from rfl, ↓reduceIte,
      getRowCell_eq (hc ⟨1, by decide⟩), hz, bne_self_eq_false, Bool.false_eq_true, Nat.ble_eq] at hcr
    unfold lb
    rw [hsc1, hsc2,
        hsc_ne ⟨0, by decide⟩ 1 (fun h => by cases h), hsc_ne ⟨2, by decide⟩ 1 (fun h => by cases h), hsc_ne ⟨3, by decide⟩ 1 (fun h => by cases h),
        hsc_ne ⟨0, by decide⟩ 2 (fun h => by cases h), hsc_ne ⟨2, by decide⟩ 2 (fun h => by cases h), hsc_ne ⟨3, by decide⟩ 2 (fun h => by cases h)]
    exact hcr
  | ⟨2, _⟩ =>
    simp only [show (2 == 0) = false from rfl, show (2 == 1) = false from rfl,
      show (2 == 2) = true from rfl, ↓reduceIte, getRowCell_eq (hc ⟨2, by decide⟩), hz,
      bne_self_eq_false, Bool.false_eq_true, Nat.ble_eq] at hcr
    unfold lb
    rw [hsc1, hsc2,
        hsc_ne ⟨0, by decide⟩ 1 (fun h => by cases h), hsc_ne ⟨1, by decide⟩ 1 (fun h => by cases h), hsc_ne ⟨3, by decide⟩ 1 (fun h => by cases h),
        hsc_ne ⟨0, by decide⟩ 2 (fun h => by cases h), hsc_ne ⟨1, by decide⟩ 2 (fun h => by cases h), hsc_ne ⟨3, by decide⟩ 2 (fun h => by cases h)]
    exact hcr
  | ⟨3, _⟩ =>
    simp only [show (3 == 0) = false from rfl, show (3 == 1) = false from rfl,
      show (3 == 2) = false from rfl, ↓reduceIte, getRowCell_eq (hc ⟨3, by decide⟩), hz,
      bne_self_eq_false, Bool.false_eq_true, Nat.ble_eq] at hcr
    unfold lb
    rw [hsc1, hsc2,
        hsc_ne ⟨0, by decide⟩ 1 (fun h => by cases h), hsc_ne ⟨1, by decide⟩ 1 (fun h => by cases h), hsc_ne ⟨2, by decide⟩ 1 (fun h => by cases h),
        hsc_ne ⟨0, by decide⟩ 2 (fun h => by cases h), hsc_ne ⟨1, by decide⟩ 2 (fun h => by cases h), hsc_ne ⟨2, by decide⟩ 2 (fun h => by cases h)]
    exact hcr

private theorem lb_step {g : Grid} (hg : validGrid g) (hf : isFalsified g = false)
    (p : Fin 4) (h : Fin 3) (hz : g p h = 0) :
    lb g ≤ lb (setCell g p h 1) + lb (setCell g p h 2) := by
  obtain ⟨pi, si, hpack, hs1, hs2, hs3⟩ := canon_exists_perm hg
  obtain ⟨pinv, hpinvL, hpinvR⟩ := perm4_inv pi
  obtain ⟨sinv, hsinvL, hsinvR⟩ := perm3_inv si
  let c := permGrid pi si g
  have hc_val : validGrid c := validGrid_perm hg pi si
  have hc_canon : canon c = packGrid c := by rw [hpack]; exact canon_perm hg pi si
  have hc_fals : isFalsified c = false := by rw [isFalsified_perm hg pi si]; exact hf
  let p' := perm4Fn pinv p
  let h' := perm3Fn sinv h
  have hc_zero : c p' h' = 0 := by simp [c, permGrid, p', h', hpinvL, hsinvL, hz]
  have hset_perm : ∀ v : Nat, permGrid pi si (setCell g p h v) = setCell c p' h' v := by
    intro v; funext q k
    simp only [permGrid, setCell, c, p', h']
    have hiff : (perm4Fn pi q = p ∧ perm3Fn si k = h) ↔ (q = perm4Fn pinv p ∧ k = perm3Fn sinv h) := by
      constructor
      · rintro ⟨hq, hk⟩
        exact ⟨by rw [← hq, hpinvR], by rw [← hk, hsinvR]⟩
      · rintro ⟨rfl, rfl⟩
        exact ⟨hpinvL p, hsinvL h⟩
    by_cases hcond : q = perm4Fn pinv p ∧ k = perm3Fn sinv h
    · have h1 := hiff.mpr hcond
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true hcond)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (mt hiff.mp hcond)), ite_eq_right_of_eq_false _ _ (eq_false hcond)]
  have hval_set : ∀ v < 3, validGrid (setCell g p h v) := by
    intro v hv q k; unfold setCell; split; exact hv; exact hg q k
  rw [← lb_perm hg pi si, ← lb_perm (hval_set 1 (by decide)) pi si,
      ← lb_perm (hval_set 2 (by decide)) pi si, hset_perm 1, hset_perm 2]
  exact lb_step_canon hc_val ⟨hs1, hs2, hs3⟩ hc_canon hc_fals p' h' hc_zero

/-! ## 5. Resolution proof leaf lower bound by induction on `ResProof` -/

private def proofLeaves {φ : CNF} {c : Clause} : ResProof φ c → Nat
  | .leaf _ => 1
  | .step p1 p2 _ => proofLeaves p1 + proofLeaves p2

private theorem size_eq_leaves {φ : CNF} {c : Clause} (p : ResProof φ c) :
    p.size + 1 = 2 * proofLeaves p := by
  induction p with
  | leaf _ => rfl
  | step p1 p2 _ ih1 ih2 =>
    simp only [ResProof.size, proofLeaves]
    omega

private theorem leaves_pos {φ : CNF} {c : Clause} (p : ResProof φ c) :
    1 ≤ proofLeaves p := by
  induction p with
  | leaf _ => exact Nat.le_refl 1
  | step p1 p2 _ ih1 _ => simp only [proofLeaves]; omega

private def Falsifies (ρ : Nat → Option Bool) (c : Clause) : Prop :=
  ∀ l ∈ c, ρ l.var = some (!l.pos)

private def updateAssign (ρ : Nat → Option Bool) (v : Nat) (b : Bool) : Nat → Option Bool :=
  fun w => if w = v then some b else ρ w

private theorem validGrid_toGrid (ρ : Nat → Option Bool) : validGrid (toGrid ρ) := by
  intro p h; unfold toGrid tritVal
  cases ρ (p.val * 3 + h.val) with
  | none => decide
  | some b => cases b <;> decide

private theorem falsifies_php_isFalsified (ρ : Nat → Option Bool) (c : Clause)
    (hc : c ∈ PHP 4 3) (hf : Falsifies ρ c) : isFalsified (toGrid ρ) = true := by
  rw [isFalsified_iff (validGrid_toGrid ρ)]
  have hlist : ∀ cl ∈ PHP 4 3,
      (∃ p : Fin 4, cl = phpPigeonClause 3 p.val) ∨
      (∃ h : Fin 3, ∃ p1 p2 : Fin 4, p1.val < p2.val ∧
        cl = [⟨phpVar 3 p1.val h.val, false⟩, ⟨phpVar 3 p2.val h.val, false⟩]) := by
    decide +kernel
  rcases hlist c hc with ⟨p, rfl⟩ | ⟨h, p1, p2, hlt, rfl⟩
  · refine Or.inl ⟨p, fun h => ?_⟩
    have hl : ⟨p.val * 3 + h.val, true⟩ ∈ phpPigeonClause 3 p.val := by
      unfold phpPigeonClause phpVar
      match h with | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ => simp
    have hρ := hf _ hl
    simp [toGrid, tritVal, hρ]
  · refine Or.inr ⟨h, p1, p2, fun heq => by subst heq; omega, ?_, ?_⟩
    · have hρ := hf ⟨phpVar 3 p1.val h.val, false⟩ (by simp)
      simp only [phpVar] at hρ
      simp [toGrid, tritVal, hρ]
    · have hρ := hf ⟨phpVar 3 p2.val h.val, false⟩ (by simp)
      simp only [phpVar] at hρ
      simp [toGrid, tritVal, hρ]

private theorem lb_le_leaves {c : Clause} (p : ResProof (PHP 4 3) c) :
    ∀ ρ : Nat → Option Bool, Falsifies ρ c → lb (toGrid ρ) ≤ proofLeaves p := by
  induction p with
  | leaf hc =>
    intro ρ hf
    have hfg := falsifies_php_isFalsified ρ _ hc hf
    unfold lb lbRows
    change (if isFalsified (toGrid ρ) then 1 else dpBST.find (canon (toGrid ρ))) ≤ 1
    rw [hfg]; simp
  | @step c1 c2 r v p1 p2 hr ih1 ih2 =>
    intro ρ hf
    rcases hr with ⟨hc1v, hc2v, hc1r, hc2r, _⟩
    cases hρv : ρ v with
    | some b =>
      cases b with
      | false =>
        have hf1 : Falsifies ρ c1 := by
          intro l hl
          by_cases hlv : l = ⟨v, true⟩
          · subst hlv; simpa using hρv
          · exact hf l (hc1r l hl hlv)
        have h1 := ih1 ρ hf1
        simp only [proofLeaves]; omega
      | true =>
        have hf2 : Falsifies ρ c2 := by
          intro l hl
          by_cases hlv : l = ⟨v, false⟩
          · subst hlv; simpa using hρv
          · exact hf l (hc2r l hl hlv)
        have h2 := ih2 ρ hf2
        simp only [proofLeaves]; omega
    | none =>
      have hf1 : Falsifies (updateAssign ρ v false) c1 := by
        intro l hl
        by_cases hlv : l = ⟨v, true⟩
        · subst hlv; simp [updateAssign]
        · have hlr := hf l (hc1r l hl hlv)
          have hne : l.var ≠ v := by intro heq; rw [heq, hρv] at hlr; cases hlr
          simp [updateAssign, hne, hlr]
      have hf2 : Falsifies (updateAssign ρ v true) c2 := by
        intro l hl
        by_cases hlv : l = ⟨v, false⟩
        · subst hlv; simp [updateAssign]
        · have hlr := hf l (hc2r l hl hlv)
          have hne : l.var ≠ v := by intro heq; rw [heq, hρv] at hlr; cases hlr
          simp [updateAssign, hne, hlr]
      by_cases hv12 : v < 12
      · by_cases hfg : isFalsified (toGrid ρ) = true
        · have hlb1 : lb (toGrid ρ) ≤ 1 := by
            unfold lb lbRows
            change (if isFalsified (toGrid ρ) then 1 else dpBST.find (canon (toGrid ρ))) ≤ 1
            rw [hfg]; simp
          have := leaves_pos p1
          simp only [proofLeaves]; omega
        · have hfgF : isFalsified (toGrid ρ) = false := Bool.eq_false_iff.mpr hfg
          let pf : Fin 4 := ⟨v / 3, by omega⟩
          let hf' : Fin 3 := ⟨v % 3, Nat.mod_lt v (by decide)⟩
          have hz : toGrid ρ pf hf' = 0 := by
            have hidx : pf.val * 3 + hf'.val = v := by simp [pf, hf']; omega
            simp [toGrid, hidx, hρv, tritVal]
          have hset1 : toGrid (updateAssign ρ v false) = setCell (toGrid ρ) pf hf' 1 := by
            funext q k
            simp only [toGrid, updateAssign, setCell]
            have hiff : q.val * 3 + k.val = v ↔ (q = pf ∧ k = hf') := by
              constructor
              · intro heq
                exact ⟨Fin.ext (by simp [pf]; omega), Fin.ext (by simp [hf']; omega)⟩
              · rintro ⟨rfl, rfl⟩; simp [pf, hf']; omega
            by_cases hqk : q = pf ∧ k = hf'
            · have h1 := hiff.mpr hqk
              rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true hqk)]; rfl
            · rw [ite_eq_right_of_eq_false _ _ (eq_false (mt hiff.mp hqk)), ite_eq_right_of_eq_false _ _ (eq_false hqk)]
          have hset2 : toGrid (updateAssign ρ v true) = setCell (toGrid ρ) pf hf' 2 := by
            funext q k
            simp only [toGrid, updateAssign, setCell]
            have hiff : q.val * 3 + k.val = v ↔ (q = pf ∧ k = hf') := by
              constructor
              · intro heq
                exact ⟨Fin.ext (by simp [pf]; omega), Fin.ext (by simp [hf']; omega)⟩
              · rintro ⟨rfl, rfl⟩; simp [pf, hf']; omega
            by_cases hqk : q = pf ∧ k = hf'
            · have h1 := hiff.mpr hqk
              rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true hqk)]; rfl
            · rw [ite_eq_right_of_eq_false _ _ (eq_false (mt hiff.mp hqk)), ite_eq_right_of_eq_false _ _ (eq_false hqk)]
          have h1 := ih1 (updateAssign ρ v false) hf1
          have h2 := ih2 (updateAssign ρ v true) hf2
          rw [hset1] at h1; rw [hset2] at h2
          have hstep := lb_step (validGrid_toGrid ρ) hfgF pf hf' hz
          simp only [proofLeaves]; omega
      · have hsame : toGrid (updateAssign ρ v false) = toGrid ρ := by
          funext q k
          have hlt : q.val * 3 + k.val < 12 := by omega
          have hne : q.val * 3 + k.val ≠ v := by omega
          simp [toGrid, updateAssign, hne]
        have h1 := ih1 (updateAssign ρ v false) hf1
        rw [hsame] at h1
        simp only [proofLeaves]; omega

private theorem lb_empty : lb (toGrid (fun _ => none)) = 43 := by decide +kernel

theorem record : ¬ PnP.Statements.L_rec_php4.Record 84 := by
  rintro ⟨p, hsz⟩
  have hleaves : 43 ≤ proofLeaves p := by
    rw [← lb_empty]
    exact lb_le_leaves p (fun _ => none) (fun _ hl => absurd hl List.not_mem_nil)
  have hrel := size_eq_leaves p
  omega

end PnP.Lemmas.L_rec_php4_not_s84
