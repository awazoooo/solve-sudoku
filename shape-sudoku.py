#!/usr/bin/env python
# -*- coding: utf-8 -*-
### Z3の結果と元のパズルを引数にとって,わかりやすく表示.
### Sudokuのサイズは81x81までなら対応

import sys
import math

# Z3の出力
res = open("shelloutput",'r')

# Sudokuのサイズ
sizetxt = open("info.txt",'r')
size = sizetxt.readline()
PUZZLESIZE = (int)(size.replace("puzzlesize=",""))

# 元のパズル
puz = open(sys.argv[1],'r')

# パズルの解のリスト
ansList = []

# 元のパズルのリスト(ansList風)
puzzle = []

# Blockのサイズ
BLOCKSIZE = (int)(math.sqrt(PUZZLESIZE))

line = res.readline()

# satかunsatかどうか -> とりあえずエラー処理は強制終了
if line.strip() == "unsat":
    print("This program is unsat.")
    sys.exit()
elif line.strip() != "sat":
    print("input error")
    sys.exit()

# values といった文字が出るまで捨てる
while True:
    if res.readline().rstrip() == "values":
        break

line = res.readline()

# z3の結果を読み取る
while line.rstrip() != "end":
    line = line.rstrip()
    line = line.replace("(","")
    line = line.replace(")","")
    line = line.split(" ")
    ansList.append(line[1])
    line = res.readline()

# 奇数行の出力
def oddLineOutput(i):
    s = "+"

    if i % BLOCKSIZE == 0:
        if len(str(PUZZLESIZE)) == 1:
            for _ in range(PUZZLESIZE):
                s += "---+"
        else:
            for _ in range(PUZZLESIZE):
                s += "----+"
        print s 
    else:
        if len(str(PUZZLESIZE)) == 1:
            for _ in range(PUZZLESIZE):
                s += "   +"
        else:
            for _ in range(PUZZLESIZE):
                s += "    +"
        print s

# 偶数行の出力        
def evenLineOutput(i,puzzleList):
    s = "|"
    l = puzzleList[i*PUZZLESIZE:(i+1)*PUZZLESIZE]
    for i in range(len(l)):
        s += " "
        s += str(l[i])
        s += " "
        if (i+1) % BLOCKSIZE == 0:
            s += "|"
        else:
            s += " "
    print s

# パズルをprint
def printPuzzle(listOfPuzzle):
    for i in range(PUZZLESIZE):
        oddLineOutput(i)
        evenLineOutput(i,listOfPuzzle)
    oddLineOutput(PUZZLESIZE)

    
# パズルの読み取り部分    
def vinit():
    i = 0
    for line in puz.readlines():
        j = 0
        # 2桁以上の数値に対応するために一時的に文字を保持
        s = ""
        for cell in line:
            # 改行
            if cell == '\n':
                if s != "":
                    # パズルのサイズが9の場合と，2桁の場合を分ける
                    if (len(str(PUZZLESIZE)) != 1) and (len(s) == 1):
                        puzzle.append("0" + s)
                        s = ""
                    else:
                        puzzle.append(s)
                        s = ""
                i += 1
                
            # 空白
            elif cell == ' ':
                if (len(str(PUZZLESIZE))) == 1:
                    puzzle.append(cell)
                else:
                    puzzle.append(" " + cell)
                j += 1
                
            # アンダースコア 
            elif cell == '_':
                if s != "":
                    # パズルのサイズが9の場合と，2桁の場合を分ける
                    if (len(str(PUZZLESIZE)) != 1) and (len(s) == 1):
                        puzzle.append("0" + s)
                        s = ""
                    else:
                        puzzle.append(s)
                        s = ""
                    j += 1
                    
            # 数値
            else:
                s += cell
                
# パズルの読み取り(9x9以下のサイズ専用)
def readPuzzle():
    for _ in range(PUZZLESIZE):
        for cell in puz.readline():
            if cell == "" or cell == '' or cell is None:
                break
            # アンダースコアor\n
            elif cell == "_" or cell == "\n":
                continue
            # 空白
            elif cell == " ":
                puzzle.append(cell)
            # 数値
            else:
                puzzle.append(str(cell))

                
vinit()
print "\n"
print "[Original Puzzle]"
printPuzzle(puzzle)
print "\n[Solved Puzzle]"
printPuzzle(ansList)
print "\n"

# 複数解の存在チェック
info = open("info.txt","r+a")
countAnswer = None
# まず、今までに解があるかを調べる
line = info.readline()
line = info.readline()
if line.strip() == "" :
    countAnswer = 1
else:    
    line = line.replace("ansNum","")
    line = line.replace("=","")
    line = line.strip()
    countAnswer = int(line) + 1

ans = str(ansList)
ans = ans.replace("[","")
ans = ans.replace("]","")
ans = ans.replace(" ","")
info.write("ansNum={0}\n".format(countAnswer))
info.write(str(ans) + "\n")
info.close()
