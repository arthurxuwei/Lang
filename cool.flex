/*
 *  The scanner definition for COOL.
 */

/*
 *  Stuff enclosed in %{ %} in the first section is copied verbatim to the
 *  output, so headers and global definitions are placed here to be visible
 * to the code in the file.  Don't remove anything that was here initially
 */
%{
#include <cool-parse.h>
#include <stringtab.h>
#include <utilities.h>

/* The compiler assumes these identifiers. */
#define yylval cool_yylval
#define yylex  cool_yylex

/* Max size of string constants */
#define MAX_STR_CONST 1025
#define YY_NO_UNPUT   /* keep g++ happy */

extern FILE *fin; /* we read from this file */

/* define YY_INPUT so we read from the FILE fin:
 * This change makes it possible to use this scanner in
 * the Cool compiler.
 */
#undef YY_INPUT
#define YY_INPUT(buf,result,max_size) \
	if ( (result = fread( (char*)buf, sizeof(char), max_size, fin)) < 0) \
		YY_FATAL_ERROR( "read() in flex scanner failed");

char string_buf[MAX_STR_CONST]; /* to assemble string constants */
char *string_buf_ptr;

extern int curr_lineno;
extern int verbose_flag;

extern YYSTYPE cool_yylval;

/*
 *  Add Your own definitions here
 */

%}

/*
 * Define names for regular expressions here.
 */
DIGIT	[0-9]
ID	[a-zA-Z0-9_]*
TYPEID	[A-Z][a-zA-Z0-9_]*
OBJECTID	[a-z][a-zA-Z0-9_]*

CLASS 	[Cc][Ll][Aa][Ss][Ss]
ELSE	else|ELSE
FI	fi|FI
IF	if|IF
IN	in|IN
INHERITS	inherits|INHERITS
LET	let|LET
LOOP	loop|LOOP
POOL	pool|POOL
THEN	then|THEN
WHILE	while|WHILE
CASE	case|CASE
ESAC	esac|ESAC
OF	of|OF
NEW	new|NEW
ISVOID	isvoid|ISVOID

FALSE	false
TRUE	true

INTEGER [0-9]+
STRING	"[^0/\]"

ASSIGN	<-
DARROW	=>
NOT	not
LE	<=

%Start COMMENT
%x INSTRING
%%

 /*
  *  Nested comments
  */
"(*"|"--" BEGIN(COMMENT);
<COMMENT>[^*\n]*	{} 
<COMMENT>"*"+[^*)\n]*	{}
<COMMENT>\n	{++curr_lineno;}
<COMMENT>"*"+")"|"-"+"-"	{ BEGIN(INITIAL); }


 /*
  *  The multiple-character operators.
  */
{DARROW}	{ return (DARROW); }
{ASSIGN}	{ return (ASSIGN); }
{LE}		{ return (LE); }

 /*
  * Keywords are case-insensitive except for the values true and false,
  * which must begin with a lower-case letter.
  */
{CLASS}	{return (CLASS);}
{ELSE}	{return (ELSE);}
{FI}	{return (FI);}	
{IF}	{return	(IF);}
{IN}	{return (IN);}
{INHERITS}	{return (INHERITS);}
{LET}	{return	(LET);}
{LOOP}	{return (LOOP);}
{POOL}	{return (POOL);}
{THEN}	{return (THEN);}
{WHILE}	{return	(WHILE);}
{CASE}	{return (CASE);}
{ESAC}	{return (ESAC);}
{OF}	{return (OF);}
{NEW}	{return	(NEW);}
{ISVOID}	{return (ISVOID);}

 /*
  *  String constants (C syntax)
  *  Escape sequence \c is accepted for all characters c. Except for 
  *  \n \t \b \f, the result is c.
  *
  */
{INTEGER}	{ cool_yylval.symbol = inttable.add_string(yytext);
			return INT_CONST; }
{STRING}	{ cool_yylval.symbol = stringtable.add_string(yytext);
			return STR_CONST; }
{FALSE}	{cool_yylval.boolean = 0; return BOOL_CONST; }
{TRUE} { cool_yylval.boolean = 1; return BOOL_CONST; }
"+"      { return ('+'); }
"-"      { return ('-'); }
"="      { return ('='); }
"<"      { return ('<'); }
\.      { return ('.'); }
"~"      { return ('~'); }
","      { return (','); }
";"      { return (';'); }
":"      { return (':'); }
")"      { return (')'); }
"@"      { return ('@'); }
"{"      { return ('{'); }
"}"      { return ('}'); }
"*"      { return ('*'); }
"("      { return ('('); }

{TYPEID}	{ cool_yylval.symbol = idtable.add_string(yytext);
			return TYPEID; }
{OBJECTID}	{ cool_yylval.symbol = idtable.add_string(yytext);
			return OBJECTID; }

\n	{ curr_lineno++; }

[\t\b\f\r \v]	{}

"*)"	{ cool_yylval.error_msg = "Umatched *)";
		return ERROR; }
\" {BEGIN(INSTRING);}
<INSTRING>\n	{ 	curr_lineno++;
			cool_yylval.error_msg = "Unterminated string constant";
			BEGIN(INITIAL);
			return ERROR; } 
<INSTRING>[\0]	{ cool_yylval.error_msg = "String contains null character";
			return ERROR; }

.	{ cool_yylval.error_msg = yytext;
		return ERROR; }
%%