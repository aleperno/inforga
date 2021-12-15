### CONJUNTOS ###
# Los meses sobre los que opero
set MESES;

### PARAMETROS ###

# La demanda de produccion de los productos A y B
param DEMANDA_PRODA{i in MESES};
param DEMANDA_PRODB{i in MESES};

# Los costos de cada persona
param costo_A1;
param costo_A2;
param costo_B1;
param costo_B2;

# Cuantas personas posee cada turno
param pers_A1;
param pers_A2;
param pers_B1;
param pers_B2;

# Cuantas unidades produce cada turno
param prod_A1;
param prod_A2;
param prod_B1;
param prod_B2;

# Turnos por mes
param turnos_por_mes;


### VARIABLES ###

var X >= 0;

# Variables de STOCK
# Stock iniciales y finales. No se permiten stocks negativos
var STOCKA_INI{m in MESES} >= 0, integer;
var STOCKB_INI{m in MESES} >= 0, integer;
var STOCKA_FIN{m in MESES} >= 0, integer;
var STOCKB_FIN{m in MESES} >= 0, integer;

# Variables de Produccion
# Cuanto necesito producir un determinado mes
var PROD_A{m in MESES} >= 0, integer;
var PROD_B{m in MESES} >= 0, integer;


# Variables de personal
## Cuantos grupos de cada producto y produccion contrato por mes
var CONTRATADOS_A1{m in MESES} >= 0, integer;
var CONTRATADOS_A2{m in MESES} >= 0, integer;
var CONTRATADOS_B1{m in MESES} >= 0, integer;
var CONTRATADOS_B2{m in MESES} >= 0, integer;

## Cuantas personas de cada producto y grupo contrato por mes
var PERSONAL_A1{m in MESES} >= 0, integer;
var PERSONAL_A2{m in MESES} >= 0, integer;
var PERSONAL_B1{m in MESES} >= 0, integer;
var PERSONAL_B2{m in MESES} >= 0, integer;

## Contratados totales por mes
var CONTRATADOS_TOT{m in MESES} >= 0, integer;

## Cuantos turnos necesito para cada produccion por mes
var TURNOS_PRODA_PROC1{m in MESES} >= 0, integer;
var TURNOS_PRODA_PROC2{m in MESES} >= 0, integer;
var TURNOS_PRODB_PROC1{m in MESES} >= 0, integer;
var TURNOS_PRODB_PROC2{m in MESES} >= 0, integer;

## Cuantos turnos disponibles tengo para cada mes
var TURNOS_DISP_A1{m in MESES} >= 0, integer;
var TURNOS_DISP_A2{m in MESES} >= 0, integer;
var TURNOS_DISP_B1{m in MESES} >= 0, integer;
var TURNOS_DISP_B2{m in MESES} >= 0, integer;

## Necesarios totales por mes
var NECESARIOS{m in MESES} >= 0, integer;

## Mappeo de contratados y la funcion que cumplen
## Por ej cuanta gente contratada de PRODA_PROC1 esta haciendo laburo de PRODB_PROC2
var A1_en_A1{m in MESES} >= 0, integer;
var A1_en_A2{m in MESES} >= 0, integer;
var A1_en_B1{m in MESES} >= 0, integer;
var A1_en_B2{m in MESES} >= 0, integer;
var A2_en_A1{m in MESES} >= 0, integer;
var A2_en_A2{m in MESES} >= 0, integer;
var A2_en_B1{m in MESES} >= 0, integer;
var A2_en_B2{m in MESES} >= 0, integer;
var B1_en_A1{m in MESES} >= 0, integer;
var B1_en_A2{m in MESES} >= 0, integer;
var B1_en_B1{m in MESES} >= 0, integer;
var B1_en_B2{m in MESES} >= 0, integer;
var B2_en_A1{m in MESES} >= 0, integer;
var B2_en_A2{m in MESES} >= 0, integer;
var B2_en_B1{m in MESES} >= 0, integer;
var B2_en_B2{m in MESES} >= 0, integer;

## Cuanta gente esta al pedo de cada grupo
var NONE_A1{m in MESES} >= 0, integer;
var NONE_A2{m in MESES} >= 0, integer;
var NONE_B1{m in MESES} >= 0, integer;
var NONE_B2{m in MESES} >= 0, integer;

## Cuanta gente esta al pedo en total
var NONE_TOT{m in MESES} >= 0, integer;


### FUNCIONAL ###
minimize z: sum{m in MESES}(PERSONAL_A1[m] * costo_A1 + PERSONAL_A2[m] * costo_A2 + PERSONAL_B1[m] * costo_B1 + PERSONAL_B2[m] * costo_B2);

### CONDICIONES ###

### CONDICIONES DE STOCK ###
# Stocks iniciales

s.t. stock_inicial_a:
    STOCKA_INI[1] = 0;

s.t. stock_inicial_b:
    STOCKB_INI[1] = 0;

s.t. stock_final_a:
    STOCKA_FIN[12] = 0;

s.t. stock_final_b:
    STOCKB_FIN[12] = 0;

# Relaciones entre stocks
s.t. relacion_stocks_a{m in MESES}:
    STOCKA_FIN[m] = STOCKA_INI[m] + PROD_A[m] - DEMANDA_PRODA[m];

s.t. relacion_stocks_b{m in MESES}:
    STOCKB_FIN[m] = STOCKB_INI[m] + PROD_B[m] - DEMANDA_PRODB[m];

s.t. relacion_ini_fin_a{i in MESES, j in MESES: i<j and i<>12 and j<>1}:
    STOCKA_INI[j] = STOCKA_FIN[i];

s.t. relacion_ini_fin_b{i in MESES, j in MESES: i<j and i<>12 and j<>1}:
    STOCKB_INI[j] = STOCKB_FIN[i];


# Cuantos turnos necesito por mes, por produccion
## Producto A Proceso 1
s.t. necesarios_A1{m in MESES}:
    TURNOS_DISP_A1[m] * prod_A1 >= PROD_A[m];

## Producto A Proceso 2
s.t. necesarios_A2{m in MESES}:
    TURNOS_DISP_A2[m] * prod_A2 >= PROD_A[m];

## Producto B Proceso 1
s.t. necesarios_B1{m in MESES}:
    TURNOS_DISP_B1[m] * prod_B1 >= PROD_B[m];

## Producto B Proceso 2
s.t. necesarios_B2{m in MESES}:
    TURNOS_DISP_B2[m] * prod_B2  >= PROD_B[m];


#/*
## Relaciono los turnos entre si
#s.t. max_turnos_a1{m in MESES}:
#    TURNOS_DISP_A1[m] = A1_en_A1[m] + A1_en_A2[m] + A1_en_B1[m] + A1_en_B2[m] + NONE_A1[m];
#
#s.t. max_turnos_a2{m in MESES}:
#    TURNOS_DISP_A2[m] = A2_en_A1[m] + A2_en_A2[m] + A2_en_B1[m] + A2_en_B2[m] + NONE_A2[m];
#
#s.t. max_turnos_b1{m in MESES}:
#    TURNOS_DISP_B1[m] = B1_en_A1[m] + B1_en_A2[m] + B1_en_B1[m] + B1_en_B2[m] + NONE_B1[m];
#
#s.t. max_turnos_b2{m in MESES}:
#    TURNOS_DISP_B2[m] = B2_en_A1[m] + B2_en_A2[m] + B2_en_B1[m] + B2_en_B2[m] + NONE_B2[m];
#
### Relaciono los turnos con lo que necesito para producir
#s.t. turnos_a1{m in MESES}:
#    TURNOS_PRODA_PROC1[m] = A1_en_A1[m] + A2_en_A1[m] + B1_en_A1[m] + B2_en_A1[m];
#
#s.t. turnos_a2{m in MESES}:
#    TURNOS_PRODA_PROC2[m] = A1_en_A2[m] + A2_en_A2[m] + B1_en_A2[m] + B2_en_A2[m];
#
#s.t. turnos_b1{m in MESES}:
#    TURNOS_PRODB_PROC1[m] = A1_en_B1[m] + A2_en_B1[m] + B1_en_B1[m] + B2_en_B1[m];
#
#s.t. turnos_b2{m in MESES}:
#    TURNOS_PRODB_PROC2[m] = A1_en_B2[m] + A2_en_B2[m] + B1_en_B2[m] + B2_en_B2[m];
#*/

## Relaciono los turnos con los contratados
s.t. turnos_contratados_a1{m in MESES}:
    TURNOS_DISP_A1[m] = CONTRATADOS_A1[m] * turnos_por_mes;

s.t. turnos_contratados_a2{m in MESES}:
    TURNOS_DISP_A2[m] = CONTRATADOS_A2[m] * turnos_por_mes;

s.t. turnos_contratados_b1{m in MESES}:
    TURNOS_DISP_B1[m] = CONTRATADOS_B1[m] * turnos_por_mes;

s.t. turnos_contratados_b2{m in MESES}:
    TURNOS_DISP_B2[m] = CONTRATADOS_B2[m] * turnos_por_mes;

##### Relacion entre los contratados ####
# Cuanta gente en total tengo contratada
s.t. contratados{m in MESES}:
    CONTRATADOS_TOT[m] = CONTRATADOS_A1[m] + CONTRATADOS_A2[m] + CONTRATADOS_B1[m] + CONTRATADOS_B2[m];

# No puedo despedir
s.t. despidos_a1{i in MESES, j in MESES: i<j and i<>12 and j<>1}:
    CONTRATADOS_A1[j] >= CONTRATADOS_A1[i];

s.t. despidos_a2{i in MESES, j in MESES: i<j and i<>12 and j<>1}:
    CONTRATADOS_A2[j] >= CONTRATADOS_A2[i];

s.t. despidos_b1{i in MESES, j in MESES: i<j and i<>12 and j<>1}:
    CONTRATADOS_B1[j] >= CONTRATADOS_B1[i];

s.t. despidos_b2{i in MESES, j in MESES: i<j and i<>12 and j<>1}:
    CONTRATADOS_B2[j] >= CONTRATADOS_B2[i];

# Relaciono personas contratadas con grupos
s.t. personal_a1{m in MESES}:
    PERSONAL_A1[m] = CONTRATADOS_A1[m] * pers_A1;

s.t. personal_a2{m in MESES}:
    PERSONAL_A2[m] = CONTRATADOS_A2[m] * pers_A2;

s.t. personal_b1{m in MESES}:
    PERSONAL_B1[m] = CONTRATADOS_B1[m] * pers_B1;

s.t. personal_b2{m in MESES}:
    PERSONAL_B2[m] = CONTRATADOS_B2[m] * pers_B2;

## TEST BASURA
#s.t. test{i in MESES, j in MESES: i<j and i<>12 and j<>1}:
#    STOCK_INI[j] >= STOCK_INI[i] + 1;

### DATOS ###
data;

set MESES := 1 2 3 4 5 6 7 8 9 10 11 12;

param DEMANDA_PRODA :=
    1 1
    2 1
    3 1
    4 1
    5 1
    6 1
    7 1
    8 1
    9 1
    10 1
    11 1
    12 12185;

param DEMANDA_PRODB :=
    1 712
    2 663
    3 684
    4 775
    5 741
    6 755
    7 1168
    8 1150
    9 1027
    10 685
    11 691
    12 588;

# Costo de horas hombre
param costo_A1 := 89;
param costo_A2 := 71;
param costo_B1 := 101;
param costo_B2 := 76;


# Cuantas personas posee cada turno
param pers_A1 := 4;
param pers_A2 := 4;
param pers_B1 := 3;
param pers_B2 := 5;


# Cuantas unidades produce cada turno
param prod_A1 := 100;
param prod_A2 := 80;
param prod_B1 := 110;
param prod_B2 := 90;

# Turnos por mes
param turnos_por_mes := 22;
