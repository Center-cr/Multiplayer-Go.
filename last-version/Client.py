
import pygame, sys, random,time
from pygame.locals import *
import numpy as np
from socket import *
import threading
import time
import re





BACKGROUNDCOLOR = (255, 255, 255)
BLACK = (255, 255, 255)
BLUE = (0, 0, 255)
CELLWIDTH = 40
CELLHEIGHT = 40
PIECEWIDTH = 47
PIECEHEIGHT = 47
BOARDX = 2
BOARDY = 2
FPS = 40
INF_VALUE = 1000000
iteration_depth = 5
HASHMAP_SIZE = 8
windowSurface2 = pygame.display.set_mode((320, 420))
# 菜单图片
background = pygame.image.load('background.png')
background = pygame.transform.smoothscale(background,(320,420))
logo = pygame.image.load('logo.png')
logo =pygame.transform.smoothscale(logo,(160,80))

buttom1 = pygame.image.load('button1.png')
buttom1 = pygame.transform.smoothscale(buttom1,(160,80))
buttom1_rect = buttom1.get_rect()
buttom1_rect.center = (80, 140)
buttom2 = pygame.image.load('button2.png')
buttom2 = pygame.transform.smoothscale(buttom2,(160,80))
buttom2_rect = buttom2.get_rect()
buttom2_rect.center = (80, 240)

buttom3 = pygame.image.load('button3.png')
buttom3 = pygame.transform.smoothscale(buttom3,(160,80))
buttom3_rect = buttom3.get_rect()
buttom3_rect.center = (80, 340)




IP = '192.168.2.95'
# 端口号
SERVER_PORT = 50000
# 定义一次从socket缓冲区最多读入512个字节数据
BUFLEN = 1024
global dataSocket, SOR, message,sure_f, row ,col,if_rec,ini_p
SOR =1
sure_f = 0
row = 0
col =1
if_rec = 0
ini_p = 0
# 实例化一个socket对象，指明协议
dataSocket = socket(AF_INET, SOCK_STREAM)
# 连接服务端socket
dataSocket.connect((IP, SERVER_PORT))
message = "sure_f0 row0 col0 for client T1"
def getNewZobrist():
    board = []
    for i in range(8):
        board.append([random.randint(0,2**HASHMAP_SIZE - 1) for i in range(8)])
    return board

def get_hashcode(hashcode,board,tile):
    for i in range(8):
        for j in range(8):
            if board[i][j] == 'black':
                hashcode ^= zobrist_black[i][j]
            elif board[i][j] == 'white':
                hashcode ^= zobrist_white[i][j]

    if tile == 'white':
        hashcode ^= zobrist_swap_player[0]
    else:
        hashcode ^= zobrist_swap_player[1]
    return hashcode
class Hashtable_Node:
    lower = -INF_VALUE
    upper = INF_VALUE
    bestmove = [0,0]
    depth = 0
class Hashtable:
    lock = 0
    deepest = Hashtable_Node()
    newest = Hashtable_Node()

hashmap = {}

zobrist_white = getNewZobrist()
zobrist_black = getNewZobrist()
zobrist_swap_player = [random.randint(0, 2 ** HASHMAP_SIZE - 1), random.randint(0, 2 ** HASHMAP_SIZE - 1)]


def hash_update(hashcode,lower,upper,bestmove,depth):
    p = hashmap.get(hashcode)
    if depth == p.deepest.depth :
        if lower > p.deepest.lower:
            p.deepest.lower = lower
            p.deepest.bestmove = bestmove
        if upper < p.deepest.upper:
            p.deepest.upper = upper
    elif depth == p.newest.depth:
        if lower > p.newest.lower:
            p.newest.lower = lower
            p.newest.bestmove = bestmove
        if upper < p.newest.upper:
            p.newest.upper = upper
    elif depth > p.deepest.depth:
        p.newest.lower = p.deepest.lower
        p.newest.upper = p.deepest.upper
        p.newest.bestmove = p.deepest.bestmove
        p.newest.depth = p.deepest.depth

        p.deepest.lower = lower
        p.deepest.upper = upper
        p.deepest.bestmove = bestmove
        p.deepest.depth = depth

def hash_get(p,depth):
    if depth == p.deepest.depth:
        return p.deepest
    elif depth == p.newest.depth:
        return p.newest
    else:
        return None

def alpha_beta_with_hashtable(board,computerTile,playerTile,flag,alpha,beta,depth):
    if flag is True:
        Tile = computerTile
    else:
        Tile = playerTile
    hashcode = 0
    hashcode = get_hashcode(hashcode,board,Tile)
    bestmove = []
    p = hashmap.get(hashcode)

    if p is not None :
        global find_number
        find_number += 1
        # print('find number is %d***********'%find_number)
        node = hash_get(p, current_depth + iteration_depth - depth)
        if node is not None:
            if node.lower > alpha:
                alpha = node.lower
                if alpha >= beta:
                    return alpha
            if node.upper < beta:
                beta = node.upper
                if beta <= alpha:
                    return beta
    else:
        global non_find_number
        non_find_number += 1
        # print('not find number is %d$$$$$$$$' % non_find_number)
        newTable = Hashtable()
        newTable.lock = hashcode
        hashmap[hashcode] = newTable
        # print('hash map size is %d??????????' %len(hashmap))

    temp = alpha_beta(board,computerTile,playerTile,flag,alpha,beta,depth)
    if isinstance(temp,float) or isinstance(temp,int):
        best_value = temp
    else:
        best_value = temp[0]
        bestmove = temp[1]
    if best_value >= beta:
        hash_update(hashcode, best_value, INF_VALUE, bestmove, current_depth + iteration_depth - depth)
    elif best_value <= alpha:
        hash_update(hashcode, -INF_VALUE, best_value, bestmove, current_depth + iteration_depth - depth)
    else:
        hash_update(hashcode, best_value, best_value, bestmove, current_depth + iteration_depth - depth)
    return best_value
# alpha_beta减枝算法
#传进来如果flag是True 那么就是computer下
#传进来flag为false 那么就是player下
def alpha_beta(board,computerTile,playerTile,flag,alpha,beta,depth):
    bestValue = -INF_VALUE
    bestMove = []
    if flag is True:
        Tile = computerTile
    else:
        Tile = playerTile
    possible = getValidMoves(board,Tile)
    for x,y in possible:
        copyBoard = getBoardCopy(board)
        makeMove(copyBoard,Tile,x,y)
        if depth <= 1:
            Value = getEvaluationOfBoard(copyBoard)[Tile]
        else:
            temp = alpha_beta(copyBoard,computerTile,playerTile,not flag,-beta,-alpha,depth-1)
            if isinstance(temp,float) or isinstance(temp,int):
                Value = -temp
            else:
                Value = -temp[0]
        if Value >= beta:
            return Value
        if Value > bestValue:
            bestValue = Value
            bestMove = [x,y]
            if Value > alpha:
                alpha = Value

    return bestValue,bestMove
def mtd(board,computerTile,playerTile,flag,alpha,beta,test,depth):
    bestValue = -INF_VALUE
    while alpha < beta:
        temp = alpha_beta(board,computerTile,playerTile,flag,test-1,test,depth)
        if isinstance(temp, float):
            bestValue = temp
        else:
            bestValue = temp[0]
    if bestValue < test:
        beta = bestValue
        test = bestValue
    else:
        alpha = bestValue
        test = bestValue + 1
    return bestValue
def pvs(board,computerTile,playerTile,flag,alpha,beta,depth):
    bestValue = -INF_VALUE
    if flag is True:
        Tile = computerTile
    else:
        Tile = playerTile
    possible = getValidMoves(board,Tile)
    for x,y in possible:
        copyBoard = getBoardCopy(board)
        makeMove(copyBoard,Tile,x,y)
        if depth <= 1:
            Value = getEvaluationOfBoard(copyBoard)[Tile]
        elif bestValue == -INF_VALUE:
            Value = -pvs(copyBoard,computerTile,playerTile,not flag,-beta,-alpha,depth-1)
        else:
            Value = -pvs(copyBoard,computerTile,playerTile,not flag,-alpha-1,-alpha,depth-1)
            if Value >alpha and Value < beta:
                alpha = Value
                Value = -pvs(copyBoard, computerTile, playerTile, not flag, -beta, -alpha, depth - 1)
        if Value >= beta:
            return Value
        if Value > bestValue:
            bestValue = Value
            if Value > alpha:
                alpha = Value
    return bestValue
# 退出
def terminate():
    pygame.quit()
    sys.exit()

# 初始化棋盘

def resetBoard(board):
    for x in range(8):
        for y in range(8):
            board[x][y] = 'none'
    #初始布局:
    board[3][3] = 'black'
    board[3][4] = 'white'
    board[4][3] = 'white'
    board[4][4] = 'black'

# 开局时建立新棋盘
def getNewBoard():
    board = []
    for i in range(8):
        board.append(['none'] * 8)
    return board

# 是否是合法走法，返回false或者此走法能够被翻转的棋子位置
def isValidMove(board, tile, xstart, ystart):
    # 如果该位置已经有棋子或者出界了，返回False
    if not isOnBoard(xstart, ystart) or board[xstart][ystart] != 'none':
        return False
    # 临时将tile 放到指定的位置
    board[xstart][ystart] = tile
    if tile == 'black':
        otherTile = 'white'
    else:
        otherTile = 'black'
    # 要被翻转的棋子
    tilesToFlip = []
    for xdirection, ydirection in [[0, 1], [1, 1], [1, 0], [1, -1], [0, -1], [-1, -1], [-1, 0], [-1, 1]]:
        x, y = xstart, ystart
        x += xdirection
        y += ydirection
        if isOnBoard(x, y) and board[x][y] == otherTile:
            x += xdirection
            y += ydirection
            if not isOnBoard(x, y):
                continue
            # 一直走到出界或不是对方棋子的位置
            while board[x][y] == otherTile:
                x += xdirection
                y += ydirection
                if not isOnBoard(x, y):
                    break
            # 出界了，则没有棋子要翻转OXXXXX
            if not isOnBoard(x, y):
                continue
            # 是自己的棋子OXXXXXXO
            if board[x][y] == tile:
                while True:
                    x -= xdirection
                    y -= ydirection
                    # 回到了起点则结束
                    if x == xstart and y == ystart:
                        break
                    # 需要翻转的棋子
                    tilesToFlip.append([x, y])
    # 将前面临时放上的棋子去掉，即还原棋盘
    board[xstart][ystart] = 'none'  # restore the empty space
    # 没有要被翻转的棋子，则走法非法。翻转棋的规则。
    if len(tilesToFlip) == 0:  # If no tiles were flipped, this is not a valid move.
        return False
    return tilesToFlip

# 是否出界
def isOnBoard(x, y):
    return x >= 0 and x <= 7 and y >= 0 and y <= 7

# 获取可落子的位置，返回这些坐标，并作出标记

def getValidMoves(board, tile):
    validMoves = []
    for x in range(8):
        for y in range(8):
            if isValidMove(board, tile, x, y) != False:
                validMoves.append([x, y])
    return validMoves

# 获取棋盘上黑白双方的棋子数
def getEvaluationOfBoard(board):
    BoardBlack = np.zeros((8,8))
    BoardWhite = np.zeros((8,8))
	# 棋盘估值表
    Vmap = np.array([[500, -25, 10, 5, 5, 10, -25, 500], [-25, -45, 1, 1, 1, 1, -45, -25], [10, 1, 3, 2, 2, 3, 1, 10],
                     [5, 1, 2, 1, 1, 2, 1, 5], [5, 1, 2, 1, 1, 2, 1, 5], [10, 1, 3, 2, 2, 3, 1, 10],
                     [-25, -45, 1, 1, 1, 1, -45, -25], [500, -25, 10, 5, 5, 10, -25, 500]])
    for x in range(8):
        for y in range(8):
            if board[x][y] == 'black':
                BoardBlack[x][y] = 1
            if board[x][y] == 'white':
                BoardWhite[x][y] = 1
    # #
    # print(BoardWhite,end='**************')
    # print(BoardBlack,end='$$$$$$$$$$$$$$$$$$$')
    BoardBlack = BoardBlack * Vmap
    BoardWhite = BoardWhite * Vmap
    BlackValue = np.sum(BoardBlack)
    WhiteValue = np.sum(BoardWhite)
    return {'black': BlackValue, 'white': WhiteValue}

def getScoreOfBoard(board):
    xscore = 0
    oscore = 0
    for x in range(8):
        for y in range(8):
            if board[x][y] == 'black':
                xscore += 1
            if board[x][y] == 'white':
                oscore += 1
    return {'black': xscore, 'white': oscore}


# 谁先走，返回turn
def whoGoesFirst():
     if random.randint(0, 1) == 0:
         return 'computer'
     else:
        return 'player'

# 将一个tile棋子放到(xstart, ystart)，返回True或False，并在board中修改值
def makeMove(board, tile, xstart, ystart):
    tilesToFlip = isValidMove(board, tile, xstart, ystart) #是否正确落子

    if tilesToFlip == False:
        return False

    board[xstart][ystart] = tile #打印出来

    for x, y in tilesToFlip:
        board[x][y] = tile

    return True

# 复制棋盘
def getBoardCopy(board):
    dupeBoard = getNewBoard()
    for x in range(8):
        for y in range(8):
            dupeBoard[x][y] = board[x][y]

    return dupeBoard

# 是否在角上
def isOnCorner(x, y):
    return (x == 0 and y == 0) or (x == 7 and y == 0) or (x == 0 and y == 7) or (x == 7 and y == 7)

# 电脑走法，AI，返回最佳走法的坐标
def getComputerMove(board, computerTile):
    # 获取所以合法走法
    flag = True
    bestMove = []
    possibleMoves = getValidMoves(board, computerTile)
    # 打乱所有合法走法
    sscore = []
    random.shuffle(possibleMoves)
    # [x, y]在角上，则优先走，因为角上的不会被再次翻转
    for x, y in possibleMoves:
        if isOnCorner(x, y):
            return [x, y]
    bestScore = -1
    for x, y in possibleMoves:
        dupeBoard = getBoardCopy(board)
        makeMove(dupeBoard, computerTile, x, y)
        #score = getScoreOfBoard(dupeBoard)[computerTile]
        # score = pvs(dupeBoard,computerTile,playerTile,flag,-INF_VALUE,INF_VALUE,iteration_depth)
        # score = mtd(dupeBoard,computerTile,playerTile,flag,-INF_VALUE,INF_VALUE,10,iteration_depth)
        score = alpha_beta_with_hashtable(dupeBoard,computerTile,playerTile,flag,-INF_VALUE,INF_VALUE,iteration_depth)
        # sscore.append(score)
        # print(sscore)
        if score is not INF_VALUE and score > bestScore:
            bestMove = [x, y]
            bestScore = score
    if len(bestMove) == 0:
        for x, y in possibleMoves:
            bestMove = [x,y]
            break

    print(bestMove)
    return bestMove


# 是否游戏结束

def isGameOver(board):
    for x in range(8):
        for y in range(8):
            if board[x][y] == 'none':
                return False

    return True

# 画出棋子，无返回值
def drawTile(board):
    for x in range(8):
        for y in range(8):
            rectDst = pygame.Rect(BOARDX + x * CELLWIDTH + 2, BOARDY + y * CELLHEIGHT + 2, PIECEWIDTH, PIECEHEIGHT)
            if mainBoard[x][y] == 'black':
                windowSurface2.blit(blackImage, rectDst, blackRect)
            elif mainBoard[x][y] == 'white':
                windowSurface2.blit(whiteImage, rectDst, whiteRect)

# 画出能够落子的位置，无返回值
def drawValidMoves(validmoves):
    for [x,y] in validMoves:
        rectDst = pygame.Rect(BOARDX + x * CELLWIDTH + 2, BOARDY + y * CELLHEIGHT + 2, PIECEWIDTH, PIECEHEIGHT)
        windowSurface2.blit(chooseImage, rectDst, chooseRect)

#游戏结束时的界面显示
def drawGameOver(board):
    scorePlayer = getScoreOfBoard(board)[playerTile]
    scoreComputer = getScoreOfBoard(board)[computerTile]
    outputStr = gameoverStr + str(scorePlayer) + ":" + str(scoreComputer)
    text = basicFont.render(outputStr, True, BLACK, BLUE)
    textRect = text.get_rect()
    textRect.centerx = windowSurface2.get_rect().centerx
    textRect.centery = windowSurface2.get_rect().centery
    windowSurface2.blit(text, textRect)
def drawWhosTurn1(board,tile):
    # print('tile',tile)
    if tile == "player":
        tile = "Player1"
    else:
        tile = "Player2"
    outstr = "it is " + tile + "'s turn"
    text = basicFont.render(outstr, True, BLACK, BLUE)
    textRect = text.get_rect()
    textRect.centerx = windowSurface2.get_rect().centerx
    textRect.centery = windowSurface2.get_rect().centery + 150
    windowSurface2.blit(text, textRect)

    scorePlayer = getScoreOfBoard(board)[playerTile]
    scoreComputer = getScoreOfBoard(board)[computerTile]
    outputStr = "Player1 vs Player2  " + str(scorePlayer) + ":" + str(scoreComputer)
    text = basicFont.render(outputStr, True, BLACK, BLUE)
    textRect = text.get_rect()
    textRect.centerx = windowSurface2.get_rect().centerx
    textRect.centery = windowSurface2.get_rect().centery + 180
    windowSurface2.blit(text, textRect)
def drawWhosTurn(board,tile):
    outstr = "it is " + tile + "'s turn"
    text = basicFont.render(outstr, True, BLACK, BLUE)
    textRect = text.get_rect()
    textRect.centerx = windowSurface2.get_rect().centerx
    textRect.centery = windowSurface2.get_rect().centery + 150
    windowSurface2.blit(text, textRect)

    scorePlayer = getScoreOfBoard(board)[playerTile]
    scoreComputer = getScoreOfBoard(board)[computerTile]
    outputStr = "Player vs Computer  " + str(scorePlayer) + ":" + str(scoreComputer)
    text = basicFont.render(outputStr, True, BLACK, BLUE)
    textRect = text.get_rect()
    textRect.centerx = windowSurface2.get_rect().centerx
    textRect.centery = windowSurface2.get_rect().centery + 180
    windowSurface2.blit(text, textRect)
def PVP():
    global mainBoard, sure_f, message, row, col,dataSocket,playerTile,computerTile,playerTile1,computerTile1,if_rec,player_color
    global turn, gameOver
    mainBoard = getNewBoard()
    resetBoard(mainBoard)
    global  validMoves
    global current_depth
    while if_rec == 0:
        pass

    if player_color =='b':
        turn = 'player'
        playerTile = 'black'#先手黑棋
        computerTile = 'white'
        playerTile1 = 'black'#先手黑棋
        computerTile1 = 'white'
    else:
        turn = 'computer'
        playerTile = 'white'
        computerTile = 'black'
        playerTile1= 'white'
        computerTile1 = 'black'
    print("PVP_player_color", player_color, "PVP", turn)

    # turn = whoGoesFirst()#随机返回“computer或player”
    # turn = 'player'
    # if turn == 'player':
    #     playerTile = 'black'#先手黑棋
    #     computerTile = 'white'
    #     playerTile1 = 'black'#先手黑棋
    #     computerTile1 = 'white'
    # else:
    #     playerTile = 'white'
    #     computerTile = 'black'
    #     playerTile1= 'white'
    #     computerTile1 = 'black'
    print("turn on begining",turn)
    gameOver = False

    while True:
        for event in pygame.event.get():
            if event.type == QUIT:
                terminate()
            # if (event.type == MOUSEBUTTONDOWN ):
            #     print(" i am here client")
            if (gameOver == False and turn == 'computer' and event.type == MOUSEBUTTONDOWN and event.button == 1):
                print("computerTile: ", computerTile)
                x, y = pygame.mouse.get_pos()
                col = int((x - BOARDX) / CELLWIDTH)
                row = int((y - BOARDY) / CELLHEIGHT)
                if makeMove(mainBoard, computerTile, col, row) == True:  ##成功行走
                    current_depth += 1
                    print(current_depth)
                    validMoves = getValidMoves(mainBoard, playerTile)
                    turn = 'player'
                    sure_f = 1
                    message = "sure_f" + str(sure_f) + " " + "row" + str(row) + " " + "col" + str(col) + " " + "T1"
                    if validMoves != []:  # 还能不能继续走
                        pass
                else:
                    if len(getValidMoves(mainBoard, computerTile)) == 0:
                        if getValidMoves(mainBoard, playerTile) != []:
                            # turn = 'player'
                            # sure_f = 1
                            # message = "sure_f" + str(sure_f) + " " + "row" + str(row) + " " + "col" + str(
                            #     col) + " " + "T1"
                            pass

                        else:
                            # sure_f = 1
                            # message = "sure_f" + str(sure_f) + " " + "row" + str(row) + " " + "col" + str(
                            #     col) + " " + "T1"
                            # print(" i am client last")
                            # turn = 'player'
                            # print("playertile here    ....", playerTile)
                            # windowSurface2.fill(BACKGROUNDCOLOR)
                            # windowSurface2.blit(boardImage, boardRect, boardRect)
                            # drawValidMoves(validMoves)
                            # drawTile(mainBoard)
                            # drawWhosTurn1(mainBoard, turn)
                            time.sleep(0.5)
                            # dataSocket.send(message)
                            gameOver = True
        print("turn here ,,,,",turn)
        windowSurface2.fill(BACKGROUNDCOLOR)
        windowSurface2.blit(boardImage, boardRect, boardRect)
        drawValidMoves(validMoves)
        drawTile(mainBoard)
        drawWhosTurn1(mainBoard, turn)
        print("playertile here    ....",playerTile)
        if isGameOver(mainBoard) or gameOver is True:
            drawGameOver(mainBoard)
        # 刷新显示与计时
        pygame.display.update()
        mainClock.tick(FPS)


#人机对战
def rjdz():
    global mainBoard
    mainBoard = getNewBoard()
    resetBoard(mainBoard)
    global  validMoves
    global current_depth
    turn = whoGoesFirst()
    if turn == 'player':
        playerTile = 'black'
        computerTile = 'white'
    else:
        playerTile = 'white'
        computerTile = 'black'
    print(turn)
    gameOver = False

    while True:
        for event in pygame.event.get():
            if event.type == QUIT:
                terminate()
            if gameOver == False and turn == 'player' and event.type == MOUSEBUTTONDOWN and event.button == 1:
                x, y = pygame.mouse.get_pos()

                col = int((x - BOARDX) / CELLWIDTH)
                row = int((y - BOARDY) / CELLHEIGHT)

                if makeMove(mainBoard, playerTile, col, row) == True:
                    current_depth += 1
                    print(current_depth)
                    validMoves = getValidMoves(mainBoard, computerTile)
                    if validMoves != []:
                        turn = 'computer'
                else:
                    if len(getValidMoves(mainBoard, playerTile)) == 0:
                        if getValidMoves(mainBoard, computerTile) != []:
                            turn = 'computer'
                        else:
                            gameOver = True
        windowSurface2.fill(BACKGROUNDCOLOR)
        windowSurface2.blit(boardImage, boardRect, boardRect)
        drawWhosTurn(mainBoard, turn)
        drawValidMoves(validMoves)
        drawTile(mainBoard)
        if isGameOver(mainBoard) or gameOver is True:
            drawGameOver(mainBoard)

        # 刷新显示与计时
        pygame.display.update()

        mainClock.tick(FPS)

        if (gameOver == False and turn == 'computer'):
            tmp = getComputerMove(mainBoard, computerTile)
            if len(tmp):
                x, y = tmp
            else:
                if getValidMoves(mainBoard, playerTile) != []:
                    turn = 'player'
                else:
                    gameOver = True
            time.sleep(1)
            makeMove(mainBoard, computerTile, x, y)
            current_depth += 1
            print(current_depth)
            # 玩家有可行的走法
            validMoves = getValidMoves(mainBoard, playerTile)
            if validMoves != []:
                turn = 'player'
def menu():
    running = True
    windowSurface2.blit(background, (0, 0))
    windowSurface2.blit(logo, (80, 0))
    windowSurface2.blit(buttom1, (80, 140))
    windowSurface2.blit(buttom2, (80, 240))
    windowSurface2.blit(buttom3, (80, 340))
    pygame.display.update()



    validMoves = [[2, 4], [3, 5], [4, 2], [5, 3]]
    current_depth = 0
    find_number = 0
    non_find_number = 0
    while running:
        windowSurface2.fill(BACKGROUNDCOLOR)
        mx, my = pygame.mouse.get_pos()
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                terminate()
            elif event.type == pygame.MOUSEBUTTONDOWN:
                if buttom1_rect.collidepoint((mx, my)):

                    rjdz()

                elif buttom2_rect.collidepoint((mx, my)):
                    PVP()
                elif buttom3_rect.collidepoint((mx,my)):
                    terminate()

# 初始化
pygame.init()
mainClock = pygame.time.Clock()
# 加载图片
boardImage = pygame.image.load('board.png')
boardRect = boardImage.get_rect()
blackImage = pygame.image.load('black.png')
blackRect = blackImage.get_rect()
whiteImage = pygame.image.load('white.png')
whiteRect = whiteImage.get_rect()


chooseImage = pygame.image.load('choose.png')
chooseRect = chooseImage.get_rect()

basicFont = pygame.font.SysFont(None, 36)

gameoverStr = 'Game Over Score '
mainBoard = getNewBoard()
resetBoard(mainBoard)

# 设置窗口界面

pygame.display.set_caption('黑白棋-客户端')

gameOver = False


def handle(rec):
    global turn, gameOver,current_depth,playerTile,computerTile,mainBoard,handle_flag,color_flag,player_color,if_rec
    global validMoves,d,t,p,playerTile1,computerTile1,ini_p
    pi_inip = re.compile(r'inip1')
    pi_T = re.compile(r'T(\d)')
    pi_sure_flag = re.compile(r'sure_f1')
    pi_color = re.compile(r'player(\w)')
    d = 0
    t = 0
    p = 0
    m = pi_sure_flag.search(rec)
    n = pi_inip.search(rec)
    print("m here",m)
    if n is not None:
        for j in range(0,len(rec)):
            if rec[j]=='i' and rec[j+1]== 'n' and rec[j+2]== 'i' and rec[j+3] == 'p' and rec[j+4] == '1':
                p =j-1
                break
        player_color = rec[p]
        print("player_color", player_color)
        if_rec = 1
    if m is not None:
        t = 1
        for i in  range(0,len(rec)):
            if rec[i] == 'f' and rec[i+1] =='1':
                d = i+2
                break
        rec = rec[d:]
    print("m there",m)
    print("reversed...........",rec)
    re_T = int(pi_T.search(rec).group(1))
    pi_row = re.compile(r'row(\d)')
    pi_col = re.compile(r'col(\d)')
    re_col = int(pi_col.search(rec).group(1))
    re_row = int(pi_row.search(rec).group(1))
    print("reversed....row",re_row)
    print("reversed....col", re_col)
    print("reversed....pi_sure_flag.search(rec)", pi_sure_flag.search(rec))
    print("reversed....re_T", re_T)
    print("reversed....t", t)

    if t and re_T == 0:

        # player_color = pi_color.search(rec).group(1)
        # print("player_color", player_color)
        # if_rec = 1

        print("sure_flag to handle")
        # playerTile = 'black'
        # computerTile = 'white'
        if turn == 'player' :
            print(playerTile)
            col = re_col
            row = re_row
            print("row",re_row,"col",re_col)
            # print("makeMove(mainBoard, playerTile, col, row) ",makeMove(mainBoard, playerTile, col, row) )
            if makeMove(mainBoard, playerTile, col, row) == True:  ##成功行走
                current_depth += 1
                print(current_depth)
                validMoves = getValidMoves(mainBoard, computerTile)
                print("makeMove is True")
                print("validMoves",validMoves)
                if validMoves != []:  # 还能不能继续走
                    turn = 'computer'
                    print("turn to computer-myself here")
            else:
                print("makeMove is Flase")
                print("validMoves", validMoves)
                if len(getValidMoves(mainBoard, playerTile)) == 0:
                    if getValidMoves(mainBoard, computerTile) != []:
                        turn = 'computer'
                        print("turn to computer-myself here")
                    else:
                        gameOver = True
            windowSurface2.fill(BACKGROUNDCOLOR)
            windowSurface2.blit(boardImage, boardRect, boardRect)
            drawWhosTurn(mainBoard, turn)
            drawValidMoves(validMoves)
            drawTile(mainBoard)
    # handle_flag = 1

def TCP_Client():
    global dataSocket, SOR, message,BUFLEN, handle_flag,sure_f,row, col

    while True:
        if SOR == 1 :
            # print("waiting for receiving...........")
            recved = dataSocket.recv(BUFLEN)
            rec = recved.decode()
            if not recved:
                break
            if rec:
                print("received", rec)
                # handle_flag = 0
                handle(rec)
                ##关键代码，需要进行延时处理，不然会出现Handle无法完全执行，又开始进行发送数据
                time.sleep(0.5)
                SOR = 0
        # time.sleep(0.3)
        if SOR == 0 :
            # if sure_f == 1:
            #     time.sleep(0.3)
            if sure_f == 1:
                time.sleep(0.3)
                temp = message
                print("Send_message", temp)
                dataSocket.send(temp.encode())
            print("sending",message)
            dataSocket.send(message.encode())
            sure_f = 0
            message = "sure_f" + str(sure_f) + " " + "row" + str(row) + " " + "col" + str(col) + " " + "T1"
            # sure_flag = 0
            # flash_flag = 0
            # regret_flag = 0
            # message = "sure_f" + str(sure_flag) + "row" + str(send_row) + " col" + str(send_col) + "flash" + str(
            #     flash_flag) + "reg" + str(regret_flag)
            # # time.sleep(0.1)
            SOR = 1






# 游戏主循环
validMoves = [[2,4],[3,5],[4,2],[5,3]]
current_depth = 0
find_number = 0
non_find_number = 0
turn = whoGoesFirst()
if turn == 'player':
                    playerTile = 'black'
                    computerTile = 'white'
else:
                    playerTile = 'white'
                    computerTile = 'black'


running = True
gameoverStr = 'Game Over Score '
client_thread = threading.Thread(target=TCP_Client)
client_thread.start()

while running:
    menu()
    for event in pygame.event.get():
        if event.type == pygame.QUIT:
            terminate()
