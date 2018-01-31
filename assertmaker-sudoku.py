#!/usr/bin/env python
# -*- coding: utf-8 -*-
###z3のプログラムを記述するプログラム
###引数としてパズルを受け取る
###パズルから生成した制約はoutput.rsに出力
#option
# -l:同一の横ライン・縦ライン・ブロックの数の合計についての追加制約
# -a:パズル内の全ての数の合計についての追加制約
# -m:複数解の存在をチェック

import sys
import math

class SolverMaker:

    def template(self):
        ###プログラムの最初に記述するテンプレ
        self.output.write(";;;written by program.\n\n")
        
        #smtの初期設定
        self.output.write(";settings\n")
        self.output.write("(set-option :produce-models true)\n\n")

        
    def vdeclare(self):
        ###変数宣言部分
        self.output.write(";declaring variables\n\n")

        #vLineListとblockListの初期化
        for _ in range(self.PUZZLESIZE):
            self.vLineList.append([])
            self.blockList.append([])

        #変数名の登録&横ライン・縦ラインごとのセルのリストのリストを作る
        for i in range(self.PUZZLESIZE):
            #横ラインごとのセルのリスト
            hline = []
            
            for j in range(self.PUZZLESIZE):
                #変数名はc0_6など(0行6列のセル)
                variableName = "c" + str(i) + "_" + str(j)
                self.variablesList.append(variableName)
                #縦ラインの変数と横ラインの変数に変数名を格納
                hline.append(variableName)
                self.vLineList[j].append(variableName)
                #Z3に与える変数宣言部分の制約
                self.output.write("(declare-const {0} Int)\n".format(variableName))
            self.hLineList.append(hline)

        ##ブロックごとのセルのリストのリストを作る
        #まず変数名のリストをBLOCKSIZE個づつに分ける
        blocksizeList = [self.variablesList[i:i+self.BLOCKSIZE] for i in range(0,self.PUZZLESIZE*self.PUZZLESIZE,self.BLOCKSIZE)]

        #まずはブロック分けのルールを作成
        #9x9では[[0,1,2],[3,4,5],[6,7,8]]というようなリストのリスト
        PUZZLESIZELIST = range(self.PUZZLESIZE)
        separaterule = [PUZZLESIZELIST[i:i+self.BLOCKSIZE] for i in range(0,self.PUZZLESIZE,self.BLOCKSIZE)]
        
        separation = []

        #flatなリストにする
        for i in range(self.BLOCKSIZE):
            for j in range(self.BLOCKSIZE):
                separation.extend(separaterule[i])

        for i in range(len(blocksizeList)):
            for j in range(self.BLOCKSIZE):
                self.blockList[separation[i]].append(blocksizeList[i][j])
                

    def rule1(self):
        ##最もシンプルな数独への制約
        ##・各マスは1~PUZZLESIZEまでのうち、1つの整数である
        ##・各行には数の重複がない
        ##・各列には数の重複がない
        ##・各ブロックには数の重複がない
        
        #変数の定義域の設定
        self.output.write("\n;setting range of variables\n\n")
        for name in self.variablesList:
            self.output.write("(assert (and (<= {0} {1}) (<= {1} {2})))\n".format(1,name,self.PUZZLESIZE))

        #横ラインの数字の独立性の設定
        self.output.write("\n;setting horizonal line distinction\n\n")
        for hline in self.hLineList:
            #まず、distinctに渡す文字列を整形
            s = ""
            for i in range(self.PUZZLESIZE):
                s += hline[i]
                s += " "
                
            self.output.write("(assert (distinct {0}))\n".format(s))        
    
        #縦ラインの数字の独立性の設定
        self.output.write("\n;setting vertical line distinction\n\n")
        for vline in self.vLineList:
            #まず、distinctに渡す文字列を整形
            s = ""
            for i in range(self.PUZZLESIZE):
                s += vline[i]
                s += " "
        
            self.output.write("(assert (distinct {0}))\n".format(s))

        #ブロックの数字の独立性の設定
        self.output.write("\n;setting block distinction\n\n")
        for block in self.blockList:
            #まず、distinctに渡す文字列を整形
            s = ""
            for i in range(self.PUZZLESIZE):
                s += block[i]
                s += " "
        
            self.output.write("(assert (distinct {0}))\n".format(s))


    def rule2(self):
        ##各行・各列・各ブロックの数字の合計に関する制約を追加
        self.output.write("\n\n;add sum of the line assertion\n\n")
        
        #各ブロック(行・列も)の数の合計
        sumOfBlock = self.PUZZLESIZE * (self.PUZZLESIZE + 1) / 2

        for hline in self.hLineList:
            #まず、distinctに渡す文字列を整形
            s = ""
            for i in range(self.PUZZLESIZE):
                s += hline[i]
                s += " "
        
            self.output.write("(assert (= (+ {0}) {1}))\n".format(s,sumOfBlock))
        
        for vline in self.vLineList:
            #まず、distinctに渡す文字列を整形
            s = ""
            for i in range(self.PUZZLESIZE):
                s += vline[i]
                s += " "
        
            self.output.write("(assert (= (+ {0}) {1}))\n".format(s,sumOfBlock))        
        
        for block in self.blockList:
            #まず、distinctに渡す文字列を整形
            s = ""
            for i in range(self.PUZZLESIZE):
                s += block[i]
                s += " "
        
            self.output.write("(assert (= (+ {0}) {1}))\n".format(s,sumOfBlock))

            
    def rule3(self):
        #パズル全体の数字の合計に関する制約を追加
        self.output.write("\n;add sum of the whole puzzle assertion\n\n")

        #1つのパズルの数の合計
        sumOfPuzzle = self.PUZZLESIZE * (self.PUZZLESIZE * (self.PUZZLESIZE + 1) / 2)
        
        s = ""
        for cell in self.variablesList:
            #まず、distinctに渡す文字列を整形
            s += str(cell) + " "

        self.output.write("(assert (= (+ {0}) {1}))\n".format(s,sumOfPuzzle))


    def vinit(self,puzzle):
        ##パズルの初期値についての制約
        self.output.write("\n;setting initialize values\n\n")

        #ここでパズルを読み込んだ結果のリストを受け取る
        initValueList = self.readPuzzle(puzzle)
        s = "(assert (= {0} {1}))\n"

        for i in range(len(initValueList)):
            if initValueList[i] != 0:
                self.output.write(s.format(self.variablesList[i],initValueList[i]))


    def readPuzzle(self,puzzle):
        ##パズルを読み込んで、初期値のリストを返す(puzzleはopenされたパズルファイル)
        #初期値がないマスは空白,iはセルの行番号,jはセルの列番号

        #初期値のリスト(Int型)
        initValueList = []
        
        i = 0
        for line in puzzle.readlines():
            j = 0
            #2桁以上の数値に対応するために一時的に文字を保持
            s = ""
            for cell in line:
                #改行
                if cell == '\n':
                    if s != "":
                        initValueList.append(int(s))
                        s = ""
                    i += 1

                #空白
                elif cell == ' ':
                    initValueList.append(0)
                    j += 1

                #アンダースコア 
                elif cell == '_':
                    if s != "":
                        initValueList.append(int(s))
                        j += 1
                        s = ""

                #数値
                else:
                    s += cell

        puzzle.seek(0)
        return initValueList
    

    def readPuzzleSize(self,puzzle):
        #パズルのサイズを読み取る(puzzleはopenされたパズルファイル)
        #(アンダースコア)の数+1をパズルのサイズとする
        size = 1
        for cell in puzzle.readline():
            if cell == '_':
                size += 1

        #puzzleは後で使うので先頭にシークしておく
        puzzle.seek(0)
        return size


    def end(self):
        ##プログラムの最後に記述
        self.output.write("\n(check-sat)\n")
        self.output.write("(get-model)\n")
        self.output.write('(echo "values")\n')

        for vName in self.variablesList:
            self.output.write("(get-value ({0}))\n".format(vName))

        self.output.write('(echo "end")\n')
        self.output.close()


    def execute(self,puzzle,option):
        ##プログラムの実行部分
        
        self.template()
        self.vdeclare()

        #最もシンプルな数独への制約
        self.rule1()

        #各行・各列・各ブロックの和がPUZZLESIZE*(PUZZLESIZE+1)/2
        if (option is not None) and ("l" in option):
            self.rule2()

        #パズル内の数字の和がPUZZLESIZE*(PUZZLESIZE*(PUZZLESIZE+1)/2)
        if (option is not None) and ("a" in option):
            self.rule3()
        
        self.vinit(puzzle)
        self.end()

        
    def __init__(self):
        ##初期設定
        #自動作成したプログラムの出力先
        self.output = open("output.rs",'w')

        #option
        option = None
        #与えられたパズル(形式は指定)
        puzzle = None
        argc = len(sys.argv)
        #optionがない場合
        if argc == 2:
            puzzle = open(sys.argv[1],'r')
        else:
            puzzle = open(sys.argv[2],'r')
            #ソルバーのoption
            option = sys.argv[1]
        
        #Sudokuのサイズ
        self.PUZZLESIZE = self.readPuzzleSize(puzzle)

        #ブロックのサイズ
        self.BLOCKSIZE = (int)(math.sqrt(self.PUZZLESIZE))

        #Sudokuのサイズが平方数でない場合は強制終了...
        if not self.BLOCKSIZE*self.BLOCKSIZE == self.PUZZLESIZE:
            sys.stderr.write("This self.puzzle's size is incorrect.")
            self.output.close()
            puzzle.close()
            sys.exit(1)

        #サイズを外部ファイルに書き出す(整形部分で利用)
        info = open("info.txt",'w')
        info.write("puzzlesize={0}\n".format(self.PUZZLESIZE))
        info.close()

        #変数名のリスト
        self.variablesList = []

        #横ライン・縦ライン・ブロックごとのセルのリストのリスト
        self.hLineList = []
        self.vLineList = []
        self.blockList = []

        #プログラムの実行
        self.execute(puzzle,option)
        

if __name__ == '__main__':

    s = SolverMaker()
    
