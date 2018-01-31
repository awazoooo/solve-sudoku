#!/usr/bin/env python
# -*- coding: utf-8 -*-

### ./solver-sudoku.py (option) puzzle.txt とすると、パズルの結果をわかりやすく表示
# option
# -m : 複数解のチェック

import sys
import os

#引数の個数
argc = len(sys.argv)
puzzle = None
option = None

# 引数が多かったり少なかったり
if argc not in range(2,4):
    if argc < 2:
        sys.stderr.write("more arguments are expected...\n")
    else:
    	sys.stderr.write("few arguments are expected...\n")
    sys.exit(1)
else:
    # optionなし
    if argc == 2:
        puzzle = sys.argv[1]
    # optionあり
    else:
        puzzle = sys.argv[2]
        option = sys.argv[1]

solve = "./assertmaker-sudoku.py "

if option is not None:
    solve += option + " " + puzzle
else:
    solve += puzzle

smt = "z3 output.rs > shelloutput"
shape = "./shape-sudoku.py " + puzzle 

os.system(solve)
os.system(smt)

# unsatの場合を弾く
output = open("shelloutput",'r')
line = output.readline()
if line.strip() == "unsat":
    sys.stderr.write("this puzzle is unsat")
    sys.exit(1)
    
os.system(shape)

# 複数解をチェック
if (option is not None) and ("m" in option):
    # satの場合はその解を除いた解が存在するかをチェック
    
    # まず，制約ファイルoutput.rsをtmp.rsにコピー
    tmpFile = open("tmp.rs",'w')
    assertFile = open("output.rs",'r')
    
    # (check-sat)と(get-model)以外をコピー
    while True:
        src = assertFile.readline()
        if src.strip() == "(check-sat)":
            break
        tmpFile.write(src)
        
    # 今までの解(とpuzzlesize)を取り出す
    origAnswer = open("info.txt",'r')
    answer = origAnswer.readline()
    size = answer.replace("puzzlesize=","")
    size = size.strip()
    size = int(size)
    
    # 解の個数チェック    
    answer = origAnswer.readline()
    answer = answer.replace("ansNum=","")
    answer = answer.strip()
    # 解の個数
    ansNum = int(answer)
    
    if ansNum >= 2:
        print 'this puzzle has two or more solutions'
        sys.exit(1)

    
    # 元の制約ファイルを削除
    assertFile.close()
    output.close()
    os.unlink("output.rs")

    # 既存の解を取得
    solution = origAnswer.readline()
    ans = solution.split(",")

    # 初期値の配置を取得
    initArr = []
    origPuzzle = open(puzzle,'r')
    for i in range(size):
        puzLine = origPuzzle.readline()
        puzLine = puzLine.replace("\n","")
        puzArr = puzLine.split("_")
        for j in range(len(puzArr)):
            # 空白でないマス(初期値がないマス)を記録
            if puzArr[j] != " ":
                initArr.append("c" + str(i) + "_" + str(j))
        
    
    # 既存の解では無いという制約を書き込む->ここでは初期値が存在するものは書き込まない．
    tmpFile.write("\n\n;solved answer\n\n")
    for i in range(size):
        for j in range(size):
            name = "c" + str(i) + "_" + str(j)
            if name not in initArr:
                s = "(assert (not (= {0} {1})))\n"
                tmpFile.write(s.format(name, int(ans[size*i+j].replace("'",""))))

    tmpFile.write("\n\n\n(check-sat)\n")
    tmpFile.write("(get-model)\n")
    # ここから解の出力部分の制約
    tmpFile.write('(echo "values")\n')
    
    for i in range(size):
        for j in range(size):
            name = "c" + str(i) + "_" + str(j)
            tmpFile.write("(get-value ({0}))\n".format(name))
    tmpFile.write('(echo "end")\n')
    tmpFile.close()
    os.rename("tmp.rs","output.rs")

    # 再びZ3を実行
    os.system(smt)
    output2 = open("shelloutput",'r')
    line2 = output2.readline()
    if line2.strip() == "sat":
        os.system(shape)
        print 'this puzzle has two or more solutions\n'
        sys.exit(1)
    else:
        print 'this puzzle has only one solution\n'
else:
    os.unlink("output.rs")
    os.unlink("info.txt")
    os.unlink("shelloutput")
