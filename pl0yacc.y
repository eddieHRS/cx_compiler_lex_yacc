////////////////////////////////////////////////////////
//声明部分
%{
#include<stdio.h>
#include<stdlib.h>
#include<malloc.h>
#include<memory.h>
#include<string.h>

#define txmax 100     /* 符号表容量 */
#define al 10         /* 标识符的最大长度 */
#define amax 2048     /* 地址上界*/
#define levmax 3      /* 最大允许过程嵌套声明层数*/
#define cxmax 200     /* 最多的虚拟机代码数 */
#define stacksize 500 /* 运行时数据栈元素最多为500个 */
#define bool int
#define true 1
#define false 0
/* 符号表中的类型 */
enum object {
    constant, 
    variable, 
    procedure,
};

/* 符号表结构 */
struct tablestruct
{
   char name[al];      /* 名字 */
   enum object kind;   /* 类型：const，var或procedure */
   int val;            /* 数值，仅const使用 */
	 int level;          /* 所处层，仅const不使用 */ 
	 int adr;            /* 地址，仅const不使用 */
	 int size;           /* 需要分配的数据区空间, 仅procedure使用 */
};
struct tablestruct table[txmax]; /* 符号表 */

/* 虚拟机代码指令 */
enum fct {
    lit,     opr,     lod, 
    sto,     cal,     ini, 
    jmp,     jpc,     
};

/* 虚拟机代码结构 */
struct instruction
{
	enum fct f;   /* 虚拟机代码指令 */
	int l;        /* 引用层与声明层的层次差 */
	int a;        /* 根据f的不同而不同 */
};
struct instruction code[cxmax]; /* 存放虚拟机代码的数组 */

int tx;         /* 符号表当前尾指针 */
int cx;         /* 虚拟机代码指针, 取值范围[0, cxmax-1] */
int px;         /* 嵌套过程索引表proctable的指针 */
int lev;        /* 层次记录 */
int proctable[3];   /* 嵌套过程索引表，最多嵌套三层 */
char id[al];
int num;
bool listswitch;   /* 显示虚拟机代码与否 */
bool tableswitch;  /* 显示符号表与否 */
bool stackswitch;  /* 是否单步查看数据栈*/

FILE* fin;      /* 输入源文件 */
FILE* ftable;	  /* 输出符号表 */
FILE* fcode;    /* 输出虚拟机代码 */
FILE* foutput;  /* 输出出错示意（如有错） */
FILE* fresult;  /* 输出执行结果 */
char fname[al];
int err;
int loopbegin = -1;  /* 记录循环开始的地方*/
int loopend = -1;    /* 记录循环结束的地方*/
int switchbreak[100]; /*记录switch中break的数组*/
int breaknum = 0;    /* 记录上面数组的个数*/
int switchnum = -1;    /* 记录 switch 后表达式的值*/
int switchjmp = -1;    /* 记录 switch jmp 的地址*/
extern int line; 

void init();
void enter(enum object k);
int position(char *s);
void setdx(int n);
void gen(enum fct x, int y, int z);
void listall();
void displaytable();
void interpret();
int base(int l, int* s, int b);
%}

////////////////////////////////////////////////////////
//辅助定义部分
%union{
char *ident;
int number;
}


%token BEGINSYM, CALLSYM, CONSTSYM, DOSYM, ENDSYM, IFSYM, ELSESYM, ODDSYM, PROCSYM, BREAKSYM
%token READSYM, THENSYM, INTSYM, WHILESYM, WRITESYM, FORSYM, CONTINUESYM
%token BECOMES, LSS, LEQ, GTR, GEQ, PLUS, MINUS, TIMES, SLASH, NOT,POW,DPLUS,DMINUS,LPAREN, RPAREN
%token MOD, TRUESYM, FALSESYM, BOOLSYM, XORSYM, XNORSYM
%token EQL, COMMA, NEQ, SEMICOLON, COLON
%token ORSYM, ANDSYM, LSHIFT, RSHIFT, EXITSYM
%token BITOR, BITAND, BITNOT, BITXOR
%token PLUSEQL, MINUSEQL, TIMESEQL, SLASHEQL, CASESYM, SWITCHSYM, DEFAULTSYM


%token <ident> IDENT
%token <number> NUMBER

%type <number> ident
%type <number> vardecl varlist vardef
%type <number> get_table_addr get_code_addr

////////////////////////////////////////////////////////
//规则部分
%%
/* 程序 */
program: block ;

/*  分程序 */
block:         {               
                table[tx].adr = cx;				  /* 记录当前层代码的开始位置 */  
                $<number>$ = cx;
               	gen(jmp, 0 , 0);            /* 产生跳转指令，跳转位置未知暂时填0 */
               }
               get_table_addr               /* 记录本层标识符的初始位置 */
               constdecl vardecl procdecls 
               {
               	code[$<number>1].a = cx;            /* 把前面生成的跳转语句的跳转位置改成当前位置 */
               	table[$2].adr = cx;         /* 记录当前过程代码地址 */
               	table[$2].size = $4 + 3;    /* 记录当前过程分配数据大小 */
               	gen(ini, 0, $4 + 3);
               	displaytable();
               }
                statement
               {
               	gen(opr, 0 , 0);               	
               	tx = proctable[px];
               }
          ;

/*  常量声明 */
constdecl: CONSTSYM INTSYM constlist SEMICOLON 
          | CONSTSYM BOOLSYM boolconstlist SEMICOLON
          |
          ;

/*  bool型的常量申明 */
boolconstlist: boolconstdef 
          | boolconstlist COMMA boolconstdef 
          ;

/* 单个bool常量 */
boolconstdef: IDENT BECOMES TRUESYM
               {
                strcpy(id,$1);   
                num = 1;
                enter(constant);
                }
              | IDENT BECOMES FALSESYM
                {
                  strcpy(id,$1);   
                  num = 0;
                  enter(constant);
                  }
              |
          ;


/* 常量声明列表 */
constlist: constdef 
          | constlist COMMA constdef 
          ;

/* 单个常量 */
constdef: IDENT BECOMES NUMBER
               {
               	strcpy(id,$1);   
               	num = $3;
               	enter(constant);
            		}
          ;

/*  变量声明 */
vardecl: vardecl INTSYM varlist SEMICOLON 
               {
                $$ = $1+$3;         /* 传递变量声明的个数 */
                setdx($1+$3);       /* 分配变量相对地址 */
               }
          | vardecl BOOLSYM varlist SEMICOLON
          		 {
                $$ = $1+$3;         /* 传递变量声明的个数 */
                setdx($1+$3);       /* 分配变量相对地址 */
               }
          | 
              {
                $$ = 0;          /* 没有变量声明 */
              } 
          ;
          		
/* 变量声明列表 */
varlist: vardef 
               {
               	$$ = $1;
               }
          | varlist COMMA vardef 
               {
               	$$ = $1 + $3;  /* 变量声明的个数相加 */
               }
          ;
         
/* 单个变量 */
vardef: IDENT 
               {
              	strcpy(id, $1); 
              	enter(variable); 
              	$$ = 1;
               }
          ;

/*  过程声明 */
procdecls: procdecls procdecl procbody 
          |  
          ;

/*  过程声明头部 */
procdecl: inc_px PROCSYM IDENT SEMICOLON
               {                 
                 strcpy(id, $3);
	               enter(procedure); 
	               proctable[px] = tx;                
               }
          ;

/*  过程声明主体 */
procbody: inc_level block dec_level_px SEMICOLON 
          ;

/*  语句 */
statement: assignmentstm 
          | callstm 
          | compoundstm 
          | ifstm 
          | whilestm 
          | readstm 
          | writestm 
          | expression
          | forstm
          | exitstm
          | breakstm
          | continuestm
          | switchstm
          |
          ;
/* switch 语句*/
switchstm: SWITCHSYM LPAREN ident RPAREN 
           BEGINSYM
           {
            if(table[$3].kind == constant)
              switchnum = table[$3].val;
            else
              switchnum = $3;
            switchjmp = cx;
            gen(jmp, 0, 0); /* 准备跳转到对应的case的语句*/
            //printf("i:%d switchjmp:%d \n ***************************\n", $3, switchjmp);
           }
           cases
           {
            int i = 0;
            while(i < breaknum){
              code[switchbreak[i]].a = cx;
              i++;
            }
            breaknum = 0;
           }
           ENDSYM
           


cases: case
       | cases SEMICOLON case
       ;

case: CASESYM NUMBER COLON 
        {
          //printf("********\n %d\n",$2);
          if(switchnum == $2) //匹配到该case
            code[switchjmp].a = cx;
        }
        statement
      |
      DEFAULTSYM COLON
        {
          if(code[switchjmp].a == 0) //未匹配到case
            code[switchjmp].a = cx;
        }
        statement
      |
       ;

/*结束语句*/
exitstm: EXITSYM 
         {
          gen(opr, 0, 0);
         }
         ;

/* BREAK 语句*/
breakstm: BREAKSYM
         {
          loopend = cx;
          switchbreak[breaknum++] = cx; // 记录switch中的break的位置
          gen(jmp, 0, 0);
         }
         ;

continuestm: CONTINUESYM
         {
          loopbegin = cx;
          gen(jmp, 0, 0);
         }
         ;

/*  赋值语句 */
assignmentstm: ident BECOMES expression 
               {
                 if ($1 == 0)
                       yyerror("Symbol does not exist");
                 else
                    {
                       if (table[$1].kind != variable)
                           yyerror("Symbol should be a variable");
                       else
                           gen(sto, lev - table[$1].level, table[$1].adr);
                    }
               }
               |
               ident PLUSEQL expression
               {
                  if ($1 == 0)
                         yyerror("Symbol does not exist");
                   else
                      {
                         if (table[$1].kind != variable)
                             yyerror("Symbol should be a variable");
                         else{
                             gen(lod, lev - table[$1].level, table[$1].adr);
                             gen(opr, 0, 2);
                             gen(sto, lev - table[$1].level, table[$1].adr);
                         }
                             
                      }
               }
               |
               ident MINUSEQL expression
               {
                  if ($1 == 0)
                         yyerror("Symbol does not exist");
                   else
                      {
                         if (table[$1].kind != variable)
                             yyerror("Symbol should be a variable");
                         else{
                             gen(lod, lev - table[$1].level, table[$1].adr);
                             gen(opr, 0, 32);
                             gen(opr, 0, 3);
                             gen(sto, lev - table[$1].level, table[$1].adr);
                         }
                             
                      }
               }
               |
               ident TIMESEQL expression
               {
                  if ($1 == 0)
                         yyerror("Symbol does not exist");
                   else
                      {
                         if (table[$1].kind != variable)
                             yyerror("Symbol should be a variable");
                         else{
                             gen(lod, lev - table[$1].level, table[$1].adr);
                             gen(opr, 0, 4);
                             gen(sto, lev - table[$1].level, table[$1].adr);
                         }
                             
                      }
               }
               |
               ident SLASHEQL expression
               {
                  if ($1 == 0)
                         yyerror("Symbol does not exist");
                   else
                      {
                         if (table[$1].kind != variable)
                             yyerror("Symbol should be a variable");
                         else{
                             gen(lod, lev - table[$1].level, table[$1].adr);
                             gen(opr, 0, 32);
                             gen(opr, 0, 5);
                             gen(sto, lev - table[$1].level, table[$1].adr);
                         }
                             
                      }
               }
          ;

/*  调用语句 */
callstm: CALLSYM ident
             {
                 if ($2 == 0)
                       yyerror("call Symbol does not exist");
                 else
                    {
                       if (table[$2].kind != procedure)
                           yyerror("Symbol should be a procedure");
                       else
                           gen (cal, lev - table[$2].level, table[$2].adr);    
                    }
              }
          ;

/* 复合语句 */
compoundstm: BEGINSYM statements ENDSYM 
          ;

/* 一条或多条语句 */
statements: statement 
          | statements SEMICOLON statement 
          ;

/* 条件语句 */
/*
ifstm: IFSYM LPAREN condition RPAREN get_code_addr 
               {
               	gen(jpc, 0, 0);
               }
       THENSYM statement 
               {
               	code[$5].a = cx;
               }
          ;
*/
/*my if*/
ifstm: IFSYM LPAREN condition RPAREN get_code_addr 
               {
                gen(jpc, 0, 0);
               }
        statement get_code_addr
               {
                gen(jmp, 0, 0);
               }
        ELSESYM 
               {
                code[$5].a = cx;
               }
        statement
               {
                code[$8].a = cx;
               }
        | IFSYM LPAREN condition RPAREN get_code_addr 
               {
                gen(jpc, 0, 0);
               }
          THENSYM statement 
               {
                code[$5].a = cx;
               }
          ;

/* 循环语句 */
whilestm: WHILESYM LPAREN get_code_addr condition RPAREN  get_code_addr 
               {
               	gen(jpc, 0 , 0);
               }
          statement
               {
               	gen(jmp, 0, $3);
               	code[$6].a = cx;
                if(loopend != -1){
                  code[loopend].a = cx;
                  loopend = -1;
                }
                if(loopbegin != -1){
                  code[loopbegin].a = $3;
                  loopbegin = -1;
                }
               }
          ;

/* for 语句*/
forstm: FORSYM LPAREN statement SEMICOLON 
        get_code_addr condition SEMICOLON
        get_code_addr 
                {
                 gen(jpc, 0 , 0);/* 判断的语句 等待回填*/
                 gen(jmp, 0 , 0);/*跳转到主体 等待回填 tag1*/
                }
        statement 
                {
                 gen(jmp, 0, $5); /*回到条件判断之前*/
                }
        RPAREN
                {
                 code[$8+1].a = cx; /*此处回填 tag1*/
                }
        statement
                {
                 gen(jmp, 0, $8 + 2); /*跳到 加一语句前*/
                 code[$8].a = cx;
                 if(loopend != -1){
                    code[loopend].a = cx;
                    loopend = -1;
                 }
                 if(loopbegin != -1){
                    code[loopbegin].a = $8 + 2;
                    loopbegin = -1;
                 }
                }
            ;

/* 读语句 */
readstm: READSYM LPAREN readvarlist RPAREN 
          ;

/* 一个或多个读语句的变量 */
readvarlist: readvar | readvarlist COMMA readvar 
          ;

/* 读语句变量 */
readvar: ident 
               {
               	gen(opr, 0, 16);
               	gen(sto, lev - table[$1].level, table[$1].adr);
               } 
          ;

/* 写语句 */
writestm: WRITESYM LPAREN writeexplist RPAREN
          ;

/* 一个或多个写语句的表达式 */
writeexplist: expression 
               {
               	gen(opr, 0, 14);
               	gen(opr, 0, 15);
               }
          | writeexplist COMMA expression
               {
               	gen(opr, 0, 14);
               	gen(opr, 0, 15);
               }
          ;

/* 条件表达式 */
condition: ODDSYM expression 
               {
               	gen(opr, 0, 6);
               }
          | expression
          | NOT expression
               {
                gen(opr, 0, 23);
               }
          | expression XORSYM expression
               {
                gen(opr, 0, 21);
               }
          | expression XNORSYM expression
               {
                gen(opr, 0, 22);
               }
          | expression EQL expression 
               {
               	gen(opr, 0, 8);
               }
          | expression NEQ expression 
               {
               	gen(opr, 0, 9);
               }
          | expression LSS expression 
               {
               	gen(opr, 0, 10);
               }
          | expression LEQ expression 
               {
               	gen(opr, 0, 13);
               }
          | expression GTR expression 
               {
               	gen(opr, 0, 12);
               }
          | expression GEQ expression 
               {
               	gen(opr, 0, 11);
               }
          | expression ORSYM expression 
               {
                gen(opr, 0, 24);
               }
          | expression ANDSYM expression 
               {
                gen(opr, 0, 25);
               }
          |
          ;

/* 表达式 */
expression: PLUS term
          | MINUS term
               {
               	gen(opr, 0, 1);
               }
          | term             
          | expression PLUS term
               {
               	gen(opr, 0, 2);
               }
          | expression MINUS term
               {
               	gen(opr, 0, 3);
               }
          ;

/* 项 */
term: factor
          | term TIMES factor
               {
               	gen(opr, 0, 4);
               }
          | term SLASH factor
               {
               	gen(opr, 0, 5);
               } 
          | term POW factor
               {
                gen(opr, 0, 17);
               } 
          | term MOD factor
               {
                gen(opr, 0, 20);
               }
          | term LSHIFT factor
               {
                gen(opr, 0, 26);
               }
          | term RSHIFT factor
               {
                gen(opr, 0, 27);
               }
          | term BITAND factor
               {
                gen(opr, 0, 28);
               }
          | term BITOR factor
               {
                gen(opr, 0, 29);
               }
          | BITNOT factor
               {
                gen(opr, 0, 30);
               }
          | term BITXOR factor
               {
                gen(opr, 0, 31);
               }
          ;

/* 因子 */
factor: ident
               { if ($1 == 0)
                       yyerror("Symbol does not exist");
                 else
                    {
                       if (table[$1].kind == procedure)
                           yyerror("Symbol should not be a procedure");
                       else
                       		{
                       			if(table[$1].kind == constant)
                       	       gen(lit, 0, table[$1].val);
                       	    else
                       	       gen(lod, lev - table[$1].level, table[$1].adr);
                       	  }
                    }
                }
          | ident DPLUS
                { if ($1 == 0)
                       yyerror("Symbol does not exist");
                 else
                    {
                       if (table[$1].kind == procedure)
                           yyerror("Symbol should not be a procedure");
                       else
                          {
                            if(table[$1].kind == constant){
                              gen(lit, 0, table[$1].val);
                              table[$1].val +=1;
                            }
                            else{
                              gen(lod, lev - table[$1].level, table[$1].adr);//拿到栈顶
                              gen(opr, 0, 18); //栈顶自增
                              gen(sto, lev - table[$1].level, table[$1].adr);//存回
                              gen(lod, lev - table[$1].level, table[$1].adr);//重新拿出
                              gen(opr, 0, 19); //栈顶自减
                            }
                               
                          }
                    }
                }
          | DPLUS ident
                { if ($2 == 0)
                       yyerror("Symbol does not exist");
                 else
                    {
                       if (table[$2].kind == procedure)
                           yyerror("Symbol should not be a procedure");
                       else
                          {
                            if(table[$2].kind == constant){
                              gen(lit, 0, table[$2].val);
                              table[$2].val +=1;
                            }
                            else{
                              gen(lod, lev - table[$2].level, table[$2].adr);//拿到栈顶
                              gen(opr, 0, 18); //栈顶自增
                              gen(sto, lev - table[$2].level, table[$2].adr);//存回
                              gen(lod, lev - table[$2].level, table[$2].adr);//重新拿出
                            }
                               
                          }
                    }
                }
          | DMINUS ident
                { if ($2 == 0)
                       yyerror("Symbol does not exist");
                 else
                    {
                       if (table[$2].kind == procedure)
                           yyerror("Symbol should not be a procedure");
                       else
                          {
                            if(table[$2].kind == constant){
                              gen(lit, 0, table[$2].val);
                              table[$2].val -=1;
                            }
                            else{
                              gen(lod, lev - table[$2].level, table[$2].adr);//拿到栈顶
                              gen(opr, 0, 19); //栈顶自增
                              gen(sto, lev - table[$2].level, table[$2].adr);//存回
                              gen(lod, lev - table[$2].level, table[$2].adr);//重新拿出
                            }
                               
                          }
                    }
                }
          | ident DMINUS
                { if ($1 == 0)
                       yyerror("Symbol does not exist");
                 else
                    {
                       if (table[$1].kind == procedure)
                           yyerror("Symbol should not be a procedure");
                       else
                          {
                            if(table[$1].kind == constant){
                              gen(lit, 0, table[$1].val);
                              table[$1].val -=1;
                            }
                            else{
                              gen(lod, lev - table[$1].level, table[$1].adr);//拿到栈顶
                              gen(opr, 0, 19); //栈顶自减
                              gen(sto, lev - table[$1].level, table[$1].adr);//存回
                              gen(lod, lev - table[$1].level, table[$1].adr);//重新拿出
                              gen(opr, 0, 18); //栈顶自增
                            }
                               
                          }
                    }
                }
          | NUMBER 
               {
               	gen(lit, 0, $1);
               }
          | TRUESYM
               {
                gen(lit, 0, 1);
               }
          | FALSESYM
               {
                gen(lit, 0, 0);
               }
          | LPAREN expression RPAREN;

ident: IDENT 
               {
                $$ = position ($1); 
               }
          ;
get_table_addr:
               {
                $$ = tx;
               } 
          ;
get_code_addr:
               {
               	$$ = cx;
               }
          ;

inc_level:
               {
               	lev++;               
               	if (lev > levmax)		/* 嵌套层数过多 */
                     yyerror("Lev is too big");    
               }
          ;
inc_px:
              {
               px++;              
              }     
          ;
dec_level_px:
              {
              	lev--;
              	px--;              
              }    
          ;


////////////////////////////////////////////////////////
//程序部分
%%
int yyerror(char *s)
{
	err = err + 1;
  printf("%s in line %d\n", s, line);
	fprintf(foutput, "%s in line %d\n", s, line);
	return 0;
}

/* 初始化 */
void init()
{
	tx = 0;
	cx = 0;
	px = 0;  
  lev = 0;   
  proctable[0] = 0;
  num = 0;
  err = 0;
}

/* 在符号表中加入一项 */
void enter(enum object k)
{
	tx = tx + 1;
	strcpy(table[tx].name, id);
	table[tx].kind = k;
	switch (k)
	{
		case constant:	/* 常量 */			
			table[tx].val = num; /* 登记常数的值 */
			break;
		case variable:	/* 变量 */
			table[tx].level = lev;	
			break;
		case procedure:	/* 过程 */
			table[tx].level = lev;
			break;
	}
}

/* 查找标识符在符号表中的位置 */
int position(char *s)
{
	int i;
	strcpy(table[0].name, s);
	i = tx;
	while(strcmp(table[i].name, s) != 0)
		i--;
	return i;
}

/* 为本层变量分配相对地址，从3开始分配 */
void setdx(int n)
{
	int i;
	for(i = 1; i <= n; i++)
		table[tx - i + 1].adr = n - i + 3;
}

/* 生成虚拟机代码 */
void gen(enum fct x, int y, int z)
{
	if (cx >= cxmax)
	{
		printf("Program is too long!\n");	/* 生成的虚拟机代码程序过长 */
		exit(1);
	}
	if ( z >= amax)
	{
		printf("Displacement address is too big!\n");	/* 地址偏移越界 */
		exit(1);
	}
	code[cx].f = x;
	code[cx].l = y;
	code[cx].a = z;
	cx++;
}

/* 输出所有目标代码  */
void listall()
{
	int i;
	char name[][5]=
	{
		{"lit"},{"opr"},{"lod"},{"sto"},{"cal"},{"int"},{"jmp"},{"jpc"},
	};
	if (listswitch)
	{
		for (i = 0; i < cx; i++)
		{
			printf("%d %s %d %d\n", i, name[code[i].f], code[i].l, code[i].a);
			fprintf(fcode,"%d %s %d %d\n", i, name[code[i].f], code[i].l, code[i].a);
			
		}
	}
}


/* 输出符号表 */
void displaytable()
{
	int i;
if (tableswitch)		/* 输出符号表 */
	{
	
	for (i = 1; i <= tx; i++)
		{
			switch (table[i].kind)
			{
				case constant:
					printf("    %d const %s ", i, table[i].name);
					printf("val=%d\n", table[i].val);
					fprintf(ftable, "    %d const %s ", i, table[i].name);
					fprintf(ftable, "val=%d\n", table[i].val);
					break;
				case variable:
					printf("    %d var   %s ", i, table[i].name);
					printf("lev=%d addr=%d\n", table[i].level, table[i].adr);
					fprintf(ftable, "    %d var   %s ", i, table[i].name);
					fprintf(ftable, "lev=%d addr=%d\n", table[i].level, table[i].adr);
					break;
				case procedure:
					printf("    %d proc  %s ", i, table[i].name);
					printf("lev=%d addr=%d size=%d\n", table[i].level, table[i].adr, table[i].size);
					fprintf(ftable,"    %d proc  %s ", i, table[i].name);
					fprintf(ftable,"lev=%d addr=%d size=%d\n", table[i].level, table[i].adr, table[i].size);
					break;
			}
		}
		printf("\n");
		fprintf(ftable, "\n");
	}

}

/* 解释程序 */
void interpret()
{
  char name[][5]=
  {
    {"lit"},{"opr"},{"lod"},{"sto"},{"cal"},{"int"},{"jmp"},{"jpc"},
  };
	int p = 0; /* 指令指针 */
	int b = 1; /* 指令基址 */
	int t = 0; /* 栈顶指针 */
	struct instruction i;	/* 存放当前指令 */
	int s[stacksize];	/* 栈 */

	printf("Start pl0\n");
	fprintf(fresult,"Start pl0\n");
	s[0] = 0; /* s[0]不用 */
	s[1] = 0; /* 主程序的三个联系单元均置为0 */
	s[2] = 0;
	s[3] = 0;
	do {
	    i = code[p];	/* 读当前指令 */
      
		p = p + 1;
		switch (i.f)
		{
			case lit:	/* 将常量a的值取到栈顶 */
				t = t + 1;
				s[t] = i.a;				
				break;
			case opr:	/* 数学、逻辑运算 */
				switch (i.a)
				{
					case 0:  /* 函数调用结束后返回 */
						t = b - 1;
						p = s[t + 3];
						b = s[t + 2];
						break;
					case 1: /* 栈顶元素取反 */
						s[t] = - s[t];
						break;
					case 2: /* 次栈顶项加上栈顶项，退两个栈元素，相加值进栈 */
						t = t - 1;
						s[t] = s[t] + s[t + 1];
						break;
					case 3:/* 次栈顶项减去栈顶项 */
						t = t - 1;
						s[t] = s[t] - s[t + 1];
						break;
					case 4:/* 次栈顶项乘以栈顶项 */
						t = t - 1;
						s[t] = s[t] * s[t + 1];
						break;
					case 5:/* 次栈顶项除以栈顶项 */
						t = t - 1;
						s[t] = s[t] / s[t + 1];
						break;
					case 6:/* 栈顶元素的奇偶判断 */
						s[t] = s[t] % 2;
						break;
					case 8:/* 次栈顶项与栈顶项是否相等 */
						t = t - 1;
						s[t] = (s[t] == s[t + 1]);
						break;
					case 9:/* 次栈顶项与栈顶项是否不等 */
						t = t - 1;
						s[t] = (s[t] != s[t + 1]);
						break;
					case 10:/* 次栈顶项是否小于栈顶项 */
						t = t - 1;
						s[t] = (s[t] < s[t + 1]);
						break;
					case 11:/* 次栈顶项是否大于等于栈顶项 */
						t = t - 1;
						s[t] = (s[t] >= s[t + 1]);
						break;
					case 12:/* 次栈顶项是否大于栈顶项 */
						t = t - 1;
						s[t] = (s[t] > s[t + 1]);
						break;
					case 13: /* 次栈顶项是否小于等于栈顶项 */
						t = t - 1;
						s[t] = (s[t] <= s[t + 1]);
						break;
					case 14:/* 栈顶值输出 */
						printf("%d", s[t]);
						fprintf(fresult, "%d", s[t]);
						t = t - 1;
						break;
					case 15:/* 输出换行符 */
						printf("\n");
						fprintf(fresult,"\n");
						break;
					case 16:/* 读入一个输入置于栈顶 */
						t = t + 1;
						printf("?");
						fprintf(fresult, "?");
						scanf("%d", &(s[t]));
						fprintf(fresult, "%d\n", s[t]);						
						break;
          case 17:/* 实现阶乘运算*/
            t = t - 1;
            int i = 0,num = s[t],pow = s[t+1];
            s[t] = 1;
            while(i < pow){
              s[t] = s[t] * num;
              i++;
            }
            break;
          case 18:/* 栈顶元素自增 */
            s[t] += 1;
            break;
          case 19:/* 栈顶元素自减 */
            s[t] -= 1;
            break;
          case 20:/* 求余运算*/
            t = t - 1;
            s[t] = s[t] % s[t + 1];
            break;
          case 21: /* 异或运算 */
            t = t - 1;
            s[t] = (s[t] == s[t + 1]) ? 0 : 1;
            break;
          case 22: /* 同或运算 */
            t = t - 1;
            s[t] = (s[t] == s[t + 1]) ? 1 : 0;
            break;
          case 23: /* 取反运算 非0 均为true*/
            s[t] = (s[t] == 0) ? 1 : 0;
            break;
          case 24: /* || or运算*/
            t = t - 1;
            s[t] = (s[t] + s[t+1] >= 1);
            break;
          case 25: /* && and运算*/
            t = t - 1;
            s[t] = (s[t] + s[t+1] >= 2);
            break;
          case 26: /* 左移运算*/
            t = t - 1;
            s[t] = (s[t] << s[t+1]);
            break;
          case 27: /* 右移运算*/
            t = t - 1;
            s[t] = (s[t] >> s[t+1]);
            break;
          case 28: /* 按位与运算*/
            t = t - 1;
            s[t] = (s[t] & s[t+1]);
            break;
          case 29: /* 按位或运算*/
            t = t - 1;
            s[t] = (s[t] | s[t+1]);
            break;
          case 30: /* 按位取反运算*/
            s[t] = ~(s[t]);
            break;
          case 31: /* 按位异或运算*/
            t = t - 1;
            s[t] = (s[t] ^ s[t+1]);
            break;
          case 32: /* 交换栈顶元素*/
            {
              int te = s[t];
              s[t] = s[t-1];
              s[t-1] = te;
              break;
            }
            
				}
				break;
			case lod:	/* 取相对当前过程的数据基地址为a的内存的值到栈顶 */
				t = t + 1;
				s[t] = s[base(i.l,s,b) + i.a];				
				break;
			case sto:	/* 栈顶的值存到相对当前过程的数据基地址为a的内存 */
				s[base(i.l, s, b) + i.a] = s[t];
				t = t - 1;
				break;
			case cal:	/* 调用子过程 */
				s[t + 1] = base(i.l, s, b);	/* 将父过程基地址入栈，即建立静态链 */
				s[t + 2] = b;	/* 将本过程基地址入栈，即建立动态链 */
				s[t + 3] = p;	/* 将当前指令指针入栈，即保存返回地址 */
				b = t + 1;	/* 改变基地址指针值为新过程的基地址 */
				p = i.a;	/* 跳转 */
				break;
			case ini:	/* 在数据栈中为被调用的过程开辟a个单元的数据区 */
				t = t + i.a;	
				break;
			case jmp:	/* 直接跳转 */
				p = i.a;
				break;
			case jpc:	/* 条件跳转 */
				if (s[t] == 0) 
					p = i.a;
				t = t - 1;
				break;
		}
    if(stackswitch){
        printf("===================\n");
        printf("当前指令条数为第 %d 条\n",p-1);
        printf("%d %s %d %d\n", p-1, name[code[p-1].f], code[p-1].l, code[p-1].a);
        printf("执行后的数据栈为：\n");
        int temp_m = t;
        while(temp_m >= 0){
          printf("no: %d num: %d\n",temp_m,s[temp_m]);
          temp_m--;
        }
        printf("是否继续下一步(Y/N)");
        scanf("%s", fname);
        stackswitch = (fname[0]=='y' || fname[0]=='Y');
    }
	} while (p != 0);
	printf("End pl0\n");
	fprintf(fresult,"End pl0\n");
}

/* 通过过程基址求上l层过程的基址 */
int base(int l, int* s, int b)
{
	int b1;
	b1 = b;
	while (l > 0)
	{
		b1 = s[b1];
		l--;
	}
	return b1;
}

int main(void)
{
	printf("Input pl/0 file?   ");
	scanf("%s", fname);		/* 输入文件名 */

	if ((fin = fopen(fname, "r")) == NULL)
	{
		printf("Can't open the input file!\n");
		exit(1);
	}	
	if ((foutput = fopen("foutput.txt", "w")) == NULL)
  {
		printf("Can't open the output file!\n");
		exit(1);
	}
	if ((ftable = fopen("ftable.txt", "w")) == NULL)
	{
		printf("Can't open ftable.txt file!\n");
		exit(1);
	}
	
	printf("List object codes?(Y/N)");	/* 是否输出虚拟机代码 */
	scanf("%s", fname);
	listswitch = (fname[0]=='y' || fname[0]=='Y');

	printf("List symbol table?(Y/N)");	/* 是否输出符号表 */
	scanf("%s", fname);
	tableswitch = (fname[0]=='y' || fname[0]=='Y');

  printf("List stack step by step?(Y/N)");
  scanf("%s", fname);
  stackswitch = (fname[0]=='y' || fname[0]=='Y');
	
	redirectInput(fin);		
	init();
  yyparse();
	if(err == 0)
	{
		printf("\n===Parsing success!===\n");
		fprintf(foutput, "\n===Parsing success!===\n");
		if ((fcode = fopen("fcode.txt", "w")) == NULL)
		{
			printf("Can't open fcode.txt file!\n");
			exit(1);
		}		

		if ((fresult = fopen("fresult.txt", "w")) == NULL)
		{
			printf("Can't open fresult.txt file!\n");
			exit(1);
		}
		
		listall();  /* 输出所有代码 */
		fclose(fcode);
		
		interpret();	/* 调用解释执行程序 */        	
		fclose(fresult);
	}
  else
	{
		printf("%d errors in PL/0 program\n", err);
		fprintf(foutput, "%d errors in PL/0 program\n", err);
		
	}
	
	fclose(ftable);
  fclose(foutput);
	fclose(fin);
	return 0;
}



