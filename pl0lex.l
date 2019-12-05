%{
#include "stdio.h"
#include "string.h"
#include "malloc.h"
#include "pl0yacc.tab.h"

int line=1;
void yyerror(char *);
int yywrap(void);

%}
%x COMMENT
%x ONE_LINE_COMMENT
%%

"/*"                     {BEGIN COMMENT;}
<COMMENT>[\n]            {line++;}
<COMMENT>"*/"            {BEGIN INITIAL;}
<COMMENT>.               {;}
"//"                     {BEGIN ONE_LINE_COMMENT;}
<ONE_LINE_COMMENT>[\n]   {line++;
						  BEGIN INITIAL;
						 }
<ONE_LINE_COMMENT>.      {;}
[ \t]					 {;}
[\n]					 {line++;}
"call"					 {return CALLSYM;}
"const"					 {return CONSTSYM;}
"do"					 {return DOSYM;}
"if"					 {return IFSYM;}
"else"                   {return ELSESYM;}
"odd"					 {return ODDSYM;}
"procedure"				 {return PROCSYM;}
"read"					 {return READSYM;}
"then"					 {return THENSYM;}
"int"					 {return INTSYM;}
"bool"                   {return BOOLSYM;}
"true"                   {return TRUESYM;}
"false"                  {return FALSESYM;}
"while"					 {return WHILESYM;}
"write"					 {return WRITESYM;}
"xor"                    {return XORSYM;}
"xnor"                   {return XNORSYM;}
"for"                    {return FORSYM;}
"exit"                   {return EXITSYM;}
"break"                  {return BREAKSYM;}
"continue"               {return CONTINUESYM;}
"case"                   {return CASESYM;}
"switch"                 {return SWITCHSYM;}
"default"                {return DEFAULTSYM;}
"repeat"                 {return REPEATSYM;}
"until"                  {return UNTILSYM;}
[A-Za-z]([A-Za-z]|[0-9])* {yylval.ident=(char *)malloc(strlen(yytext)+1);
                            strcpy(yylval.ident,yytext);
                            return IDENT;
						 }
[0-9]+					 {yylval.number=atoi(yytext);
	 						return NUMBER;
	 				     }

"=" 					 {return BECOMES;}
"<"	    				 {return LSS;}
"<="					 {return LEQ;}
">"	    				 {return GTR;}
">="					 {return GEQ;}
"++"    				 {return DPLUS;}
"--"   					 {return DMINUS;}
"+"	   					 {return PLUS;}
"-"	  					 {return MINUS;}
"*"	    				 {return TIMES;}
"**"   				     {return POW;}
"/"	                     {return SLASH;}
"<<"                     {return LSHIFT;}
">>"                     {return RSHIFT;}
"&"                      {return BITAND;}
"|"                      {return BITOR;}
"^"                      {return BITXOR;}
"~"                      {return BITNOT;}
"%"                      {return MOD;}
"("	    				 {return LPAREN;}
")"  	                 {return RPAREN;}
"{"     				 {return BEGINSYM;}
"}"                      {return ENDSYM;}
"=="					 {return EQL;}
","	    				 {return COMMA;}
"!="   					 {return NEQ;}
"+="                     {return PLUSEQL;}
"-="                     {return MINUSEQL;}
"*="                     {return TIMESEQL;}
"/="                     {return SLASHEQL;}


"!"                      {return NOT;}
";" 					 {return SEMICOLON;}
":"                      {return COLON;}
"||"                     {return ORSYM;}
"&&"                     {return ANDSYM;}
.	   					 {yyerror("Unknown character!");}

%%

void redirectInput(FILE *input)
{
	yyin=input;
}

int yygetchar(void)
{
	int ret;
	ret = getc(yyin);
	printf("%c",ret);
	return ret;
}

int yywrap(void)
{
	return 1;
}