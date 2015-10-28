header {* Tema 3: Deducción natural proposicional con Isabelle/HOL *}

theory T3
imports Main 
begin

text {*
  En este tema se presentan los ejemplos del tema de deducción natural
  proposicional siguiendo la presentación de Huth y Ryan en su libro
  "Logic in Computer Science" http://goo.gl/qsVpY y, más concretamente,
  a la forma como se explica en la asignatura de "Lógica informática" (LI) 
  http://goo.gl/AwDiv
 
  La página al lado de cada ejemplo indica la página de las transparencias 
  donde se encuentra la demostración. *}

subsection {* Reglas de la conjunción *}

text {* 
  Ejemplo 1 (p. 4). Demostrar que
     p \<and> q, r \<turnstile> q \<and> r.
  *}     

-- "La demostración detallada es"
lemma ejemplo_1_1:
  assumes 1: "p \<and> q" and
          2: "r" 
  shows "q \<and> r"     
proof -
  have 3: "q" using 1 by (rule conjunct2)
  show 4: "q \<and> r" using 3 2 by (rule conjI)
qed
thm ejemplo_1_1
text {*
  Notas sobre el lenguaje: En la demostración anterior se ha usado
  · "assumes" para indicar las hipótesis,
  · "and" para separar las hipótesis,
  · "shows" para indicar la conclusión,
  · "proof" para iniciar la prueba,
  · "qed" para terminar la pruebas,
  · "-" (después de "proof") para no usar el método por defecto,
  · "have" para establecer un paso,
  · "using" para usar hechos en un paso,
  · "by (rule ..)" para indicar la regla con la que se peueba un hecho,
  · "show" para establecer la conclusión.

  Notas sobre la lógica: Las reglas de la conjunción son
  · conjI:      \<lbrakk>P; Q\<rbrakk> \<Longrightarrow> P \<and> Q
  · conjunct1:  P \<and> Q \<Longrightarrow> P
  · conjunct2:  P \<and> Q \<Longrightarrow> Q  
*}

text {* Se pueden dejar implícitas las reglas como sigue *}

lemma ejemplo_1_2:
  assumes 1: "p \<and> q" and 
          2: "r" 
  shows "q \<and> r"     
proof -
  have 3: "q" using 1 .. 
  show 4: "q \<and> r" using 3 2 ..
qed

text {*
  Nota sobre el lenguaje: En la demostración anterior se ha usado
  · ".." para indicar que se prueba por la regla correspondiente. *}

text {* Se pueden eliminar las etiquetas como sigue *}

lemma ejemplo_1_3:
  assumes "p \<and> q" 
          "r" 
  shows   "q \<and> r"     
proof -
  have "q" using assms(1) ..
  thus "q \<and> r" using assms(2) ..
qed

text {*
  Nota sobre el lenguaje: En la demostración anterior se ha usado
  · "assms(n)" para indicar la hipótesis n y
  · "thus" para demostrar la conclusión usando el hecho anterior.
  Además, no es necesario usar and entre las hipótesis. *}

text {* Se puede automatizar la demostración como sigue *}
  
lemma ejemplo_1_4:
  assumes "p \<and> q" 
          "r" 
  shows   "q \<and> r"     
using assms
by auto

text {*
  Nota sobre el lenguaje: En la demostración anterior se ha usado
  · "assms" para indicar las hipótesis y
  · "by auto" para demostrar la conclusión automáticamente. *}

text {* Se puede automatizar totalmente la demostración como sigue *}

lemma ejemplo_1_5:
  "\<lbrakk>p \<and> q; r\<rbrakk> \<Longrightarrow> q \<and> r"
by auto

text {*
  Nota sobre el lenguaje: En la demostración anterior se ha usado
  · "\<lbrakk> ... \<rbrakk>" para representar las hipótesis,
  · ";" para separar las hipótesis y
  · "\<Longrightarrow>" para separar las hipótesis de la conclusión. *}

text {* Se puede hacer la demostración por razonamiento hacia atrás,
  como sigue *}

lemma ejemplo_1_6:
  assumes "p \<and> q" 
      and "r" 
  shows   "q \<and> r"     
proof (rule conjI)
  show "q" using assms(1) by (rule conjunct2)
next
  show "r" using assms(2) by this
qed

text {*
  Nota sobre el lenguaje: En la demostración anterior se ha usado
  · "proof (rule r)" para indicar que se hará la demostración con la
    regla r,
  · "next" para indicar el comienzo de la prueba del siguiente
    subobjetivo,
  · "this" para indicar el hecho actual. *}

text {* Se pueden dejar implícitas las reglas como sigue *}

lemma ejemplo_1_7:
  assumes "p \<and> q" 
          "r" 
  shows   "q \<and> r"     
proof 
  show "q" using assms(1) ..
next
  show "r" using assms(2) . 
qed

text {*
  Nota sobre el lenguaje: En la demostración anterior se ha usado
  · "." para indicar por el hecho actual. *}

subsection {* Reglas de la doble negación *}

text {*
  La regla de eliminación de la doble negación es
  · notnotD: \<not>\<not> P \<Longrightarrow> P

  Para ajustarnos al tema de LI vamos a introducir la siguiente regla de
  introducción de la doble negación
  · notnotI: P \<Longrightarrow> \<not>\<not> P
  aunque, de momento, no detallamos su demostración.
*}

lemma notnotI [intro!]: "P \<Longrightarrow> \<not>\<not> P"
by auto

text {*
  Ejemplo 2. (p. 5)
       p, \<not>\<not>(q \<and> r) \<turnstile> \<not>\<not>p \<and> r
*}

-- "La demostración detallada es"
lemma ejemplo_2_1:
  assumes 1: "p" and
          2: "\<not>\<not>(q \<and> r)" 
  shows      "\<not>\<not>p \<and> r"
proof -
  have 3: "\<not>\<not>p" using 1 by (rule notnotI)
  have 4: "q \<and> r" using 2 by (rule notnotD)
  have 5: "r" using 4 by (rule conjunct2)
  show 6: "\<not>\<not>p \<and> r" using 3 5 by (rule conjI)
qed        

-- "La demostración estructurada es"
lemma ejemplo_2_2:
  assumes "p" 
          "\<not>\<not>(q \<and> r)" 
  shows   "\<not>\<not>p \<and> r"
proof -
  have  "\<not>\<not>p" using assms(1) ..
  have  "q \<and> r" using assms(2) by (rule notnotD)
  hence "r" ..
  with `\<not>\<not>p` show  "\<not>\<not>p \<and> r" ..
qed        

text {*
  Nota sobre el lenguaje: En la demostración anterior se ha usado
  · "hence" para indicar que se tiene por el hecho anterior,
  · `...` para referenciar un hecho y
  · "with P show Q" para indicar que con el hecho anterior junto con el
    hecho P se demuestra Q. *}

-- "La demostración automática es"
lemma ejemplo_2_3:
  assumes "p" 
          "\<not>\<not>(q \<and> r)" 
  shows   "\<not>\<not>p \<and> r"
using assms
by auto

text {* Se puede demostrar hacia atrás *}

lemma ejemplo_2_4:
  assumes "p" 
          "\<not>\<not>(q \<and> r)" 
  shows   "\<not>\<not>p \<and> r"
proof  (rule conjI)
  show "\<not>\<not>p" using assms(1) by (rule notnotI)
next
  have "q \<and> r" using assms(2) by (rule notnotD) 
  thus "r" by (rule conjunct2)
qed 

text {* Se puede eliminar las reglas en la demostración anterior, como
  sigue: *}

lemma ejemplo_2_5:
  assumes "p" 
          "\<not>\<not>(q \<and> r)" 
  shows   "\<not>\<not>p \<and> r"
proof 
  show "\<not>\<not>p" using assms(1) ..
next
  have "q \<and> r" using assms(2) by (rule notnotD) 
  thus "r" .. 
qed

subsection {* Regla de eliminación del condicional *}

text {*
  La regla de eliminación del condicional es la regla del modus ponens
  · mp: \<lbrakk>P \<longrightarrow> Q; P\<rbrakk> \<Longrightarrow> Q 
*}

text {* 
  Ejemplo 3. (p. 6) Demostrar que
     \<not>p \<and> q, \<not>p \<and> q \<longrightarrow> r \<or> \<not>p \<turnstile> r \<or> \<not>p
*}

-- "La demostración detallada es"
lemma ejemplo_3_1:
  assumes 1: "\<not>p \<and> q" and 
          2: "\<not>p \<and> q \<longrightarrow> r \<or> \<not>p" 
  shows      "r \<or> \<not>p"
proof -
  show "r \<or> \<not>p" using 2 1 by (rule mp)
qed    

-- "La demostración estructurada es"
lemma ejemplo_3_2:
  assumes "\<not>p \<and> q"
          "\<not>p \<and> q \<longrightarrow> r \<or> \<not>p" 
  shows   "r \<or> \<not>p"
proof -
  show "r \<or> \<not>p" using assms(2,1) ..
qed    

-- "La demostración automática es"
lemma ejemplo_3_3:
  assumes "\<not>p \<and> q"
          "\<not>p \<and> q \<longrightarrow> r \<or> \<not>p" 
  shows   "r \<or> \<not>p"
using assms
by auto

text {* 
  Ejemplo 4 (p. 6) Demostrar que
     p, p \<longrightarrow> q, p \<longrightarrow> (q \<longrightarrow> r) \<turnstile> r
 *}

-- "La demostración detallada es"
lemma ejemplo_4_1:
  assumes 1: "p" and 
          2: "p \<longrightarrow> q" and 
          3: "p \<longrightarrow> (q \<longrightarrow> r)" 
  shows "r"
proof -
  have 4: "q" using 2 1 by (rule mp)
  have 5: "q \<longrightarrow> r" using 3 1 by (rule mp)
  show 6: "r" using 5 4 by (rule mp)
qed

-- "La demostración estructurada es"
lemma ejemplo_4_2:
  assumes "p"
          "p \<longrightarrow> q"
          "p \<longrightarrow> (q \<longrightarrow> r)" 
  shows "r"
proof -
  have "q" using assms(2,1) .. 
  have "q \<longrightarrow> r" using assms(3,1) ..
  thus "r" using `q` ..
qed

-- "La demostración automática es"
lemma ejemplo_4_3:
  "\<lbrakk>p; p \<longrightarrow> q; p \<longrightarrow> (q \<longrightarrow> r)\<rbrakk> \<Longrightarrow> r"
by auto

subsection {* Regla derivada del modus tollens *}

text {*
  Para ajustarnos al tema de LI vamos a introducir la regla del modus
  tollens
  · mt: \<lbrakk>F \<longrightarrow> G; \<not>G\<rbrakk> \<Longrightarrow> \<not>F 
  aunque, de momento, sin detallar su demostración.
*}

lemma mt: "\<lbrakk>F \<longrightarrow> G; \<not>G\<rbrakk> \<Longrightarrow> \<not>F"
by auto

text {*
  Ejemplo 5 (p. 7). Demostrar
     p \<longrightarrow> (q \<longrightarrow> r), p, \<not>r \<turnstile> \<not>q
 *}

-- "La demostración detallada es"
lemma ejemplo_5_1:
  assumes 1: "p \<longrightarrow> (q \<longrightarrow> r)" and 
          2: "p" and 
          3: "\<not>r" 
  shows "\<not>q"
proof -
  have 4: "q \<longrightarrow> r" using 1 2 by (rule mp)
  show "\<not>q" using 4 3 by (rule mt)
qed    

-- "La demostración estructurada es"
lemma ejemplo_5_2:
  assumes "p \<longrightarrow> (q \<longrightarrow> r)"
          "p"
          "\<not>r" 
  shows   "\<not>q"
proof -
  have "q \<longrightarrow> r" using assms(1,2) ..
  thus "\<not>q" using assms(3) by (rule mt)
qed    

-- "La demostración automática es"
lemma ejemplo_5_3:
  assumes "p \<longrightarrow> (q \<longrightarrow> r)"
          "p"
          "\<not>r" 
  shows   "\<not>q"
using assms
by auto

text {* 
  Ejemplo 6. (p. 7) Demostrar 
     \<not>p \<longrightarrow> q, \<not>q \<turnstile> p
*}

-- "La demostración detallada es"
lemma ejemplo_6_1:
  assumes 1: "\<not>p \<longrightarrow> q" and 
          2: "\<not>q" 
  shows "p"
proof -
  have 3: "\<not>\<not>p" using 1 2 by (rule mt)
  show "p" using 3 by (rule notnotD)
qed

-- "La demostración estructurada es"
lemma ejemplo_6_2:
  assumes "\<not>p \<longrightarrow> q"
          "\<not>q" 
  shows   "p"
proof -
  have "\<not>\<not>p" using assms(1,2) by (rule mt)
  thus "p" by (rule notnotD)
qed

-- "La demostración automática es"
lemma ejemplo_6_3:
  "\<lbrakk>\<not>p \<longrightarrow> q; \<not>q\<rbrakk> \<Longrightarrow> p"
by auto

text {* 
  Ejemplo 7. (p. 7) Demostrar
     p \<longrightarrow> \<not>q, q \<turnstile> \<not>p
  *}

-- "La demostración detallada es"
lemma ejemplo_7_1:
  assumes 1: "p \<longrightarrow> \<not>q" and 
          2: "q" 
  shows "\<not>p"
proof -
  have 3: "\<not>\<not>q" using 2 by (rule notnotI)
  show "\<not>p" using 1 3 by (rule mt)
qed

-- "La demostración detallada es"
lemma ejemplo_7_2:
  assumes "p \<longrightarrow> \<not>q"
          "q" 
  shows   "\<not>p"
proof -
  have "\<not>\<not>q" using assms(2) by (rule notnotI)
  with assms(1) show "\<not>p" by (rule mt)
qed

-- "La demostración estructurada es"
lemma ejemplo_7_3:
  "\<lbrakk>p \<longrightarrow> \<not>q; q\<rbrakk> \<Longrightarrow> \<not>p"
by auto

subsection {* Regla de introducción del condicional *}

text {*
  La regla de introducción del condicional es
  · impI: (P \<Longrightarrow> Q) \<Longrightarrow> P \<longrightarrow> Q
*}

text {* 
  Ejemplo 8. (p. 8) Demostrar
     p \<longrightarrow> q \<turnstile> \<not>q \<longrightarrow> \<not>p
*}

-- "La demostración detallada es"
lemma ejemplo_8_1:
  assumes 1: "p \<longrightarrow> q" 
  shows "\<not>q \<longrightarrow> \<not>p"
proof -
  { assume 2: "\<not>q"
    have "\<not>p" using 1 2 by (rule mt) } 
  thus "\<not>q \<longrightarrow> \<not>p" by (rule impI)
qed    

text {*
  Nota sobre el lenguaje: En la demostración anterior se ha usado
  · "{ ... }" para representar una caja. *}

-- "La demostración estructurada es"
lemma ejemplo_8_2:
  assumes "p \<longrightarrow> q" 
  shows "\<not>q \<longrightarrow> \<not>p"
proof 
  assume "\<not>q"
  with assms show "\<not>p" by (rule mt)
qed    

-- "La demostración automática es"
lemma ejemplo_8_3:
  assumes "p \<longrightarrow> q" 
  shows "\<not>q \<longrightarrow> \<not>p"
using assms
by auto

text {* 
  Ejemplo 9. (p. 9) Demostrar
     \<not>q \<longrightarrow> \<not>p \<turnstile> p \<longrightarrow> \<not>\<not>q
*}

-- "La demostración detallada es"
lemma ejemplo_9_1: 
  assumes 1: "\<not>q \<longrightarrow> \<not>p" 
  shows "p \<longrightarrow> \<not>\<not>q"   
proof -
  { assume 2: "p"
    have 3: "\<not>\<not>p" using 2 by (rule notnotI)
    have "\<not>\<not>q" using 1 3 by (rule mt) } 
  thus "p \<longrightarrow> \<not>\<not>q" by (rule impI)
qed

-- "La demostración estructurada es"
lemma ejemplo_9_2:
  assumes "\<not>q \<longrightarrow> \<not>p" 
  shows    "p \<longrightarrow> \<not>\<not>q"   
proof 
  assume "p"
  hence "\<not>\<not>p" by (rule notnotI)
  with assms show "\<not>\<not>q" by (rule mt)
qed

-- "La demostración automática es"
lemma ejemplo_9_3:
  assumes "\<not>q \<longrightarrow> \<not>p" 
  shows "p \<longrightarrow> \<not>\<not>q"   
using assms
by auto

text {* 
  Ejemplo 10 (p. 9). Demostrar
     \<turnstile> p \<longrightarrow> p
*}

-- "La demostración detallada es"
lemma ejemplo_10_1:
  "p \<longrightarrow> p"
proof -
  { assume 1: "p"
    have "p" using 1 by this }
  thus "p \<longrightarrow> p" by (rule impI) 
qed

-- "La demostración estructurada es"
lemma ejemplo_10_2:
  "p \<longrightarrow> p"
proof (rule impI)
qed

-- "La demostración automática es"
lemma ejemplo_10_3:
  "p \<longrightarrow> p"
by auto

text {*
  Ejemplo 11 (p. 10) Demostrar
     \<turnstile> (q \<longrightarrow> r) \<longrightarrow> ((\<not>q \<longrightarrow> \<not>p) \<longrightarrow> (p \<longrightarrow> r))
 *}

-- "La demostración detallada es"
lemma ejemplo_11_1:
  "(q \<longrightarrow> r) \<longrightarrow> ((\<not>q \<longrightarrow> \<not>p) \<longrightarrow> (p \<longrightarrow> r))"
proof -
  { assume 1: "q \<longrightarrow> r"
    { assume 2: "\<not>q \<longrightarrow> \<not>p"
      { assume 3: "p"
        have 4: "\<not>\<not>p" using 3 by (rule notnotI)
        have 5: "\<not>\<not>q" using 2 4 by (rule mt)
        have 6: "q" using 5 by (rule notnotD)
        have "r" using 1 6 by (rule mp) } 
      hence "p \<longrightarrow> r" by (rule impI) } 
    hence "(\<not>q \<longrightarrow> \<not>p) \<longrightarrow> p \<longrightarrow> r" by (rule impI) } 
  thus "(q \<longrightarrow> r) \<longrightarrow> ((\<not>q \<longrightarrow> \<not>p) \<longrightarrow> p \<longrightarrow> r)" by (rule impI)
qed

-- "La demostración hacia atrás es"
lemma ejemplo_11_2:
  "(q \<longrightarrow> r) \<longrightarrow> ((\<not>q \<longrightarrow> \<not>p) \<longrightarrow> (p \<longrightarrow> r))"
proof (rule impI)
  assume 1: "q \<longrightarrow> r"
  show "(\<not>q \<longrightarrow> \<not>p) \<longrightarrow> (p \<longrightarrow> r)"
  proof (rule impI)
    assume 2: "\<not>q \<longrightarrow> \<not>p"
    show "p \<longrightarrow> r"
    proof (rule impI)
      assume 3: "p"
      have 4: "\<not>\<not>p" using 3 by (rule notnotI)
      have 5: "\<not>\<not>q" using 2 4 by (rule mt)
      have 6: "q" using 5 by (rule notnotD)
      show "r" using 1 6 by (rule mp)
    qed
  qed
qed

-- "La demostración hacia atrás con reglas implícitas es"
lemma ejemplo_11_3:
  "(q \<longrightarrow> r) \<longrightarrow> ((\<not>q \<longrightarrow> \<not>p) \<longrightarrow> (p \<longrightarrow> r))"
proof
  assume 1: "q \<longrightarrow> r"
  show "(\<not>q \<longrightarrow> \<not>p) \<longrightarrow> (p \<longrightarrow> r)"
  proof
    assume 2: "\<not>q \<longrightarrow> \<not>p"
    show "p \<longrightarrow> r"
    proof
      assume 3: "p"
      have 4: "\<not>\<not>p" using 3 ..
      have 5: "\<not>\<not>q" using 2 4 by (rule mt)
      have 6: "q" using 5 by (rule notnotD)
      show "r" using 1 6 ..
    qed
  qed
qed

-- "La demostración sin etiquetas es" 
lemma ejemplo_11_4:
  "(q \<longrightarrow> r) \<longrightarrow> ((\<not>q \<longrightarrow> \<not>p) \<longrightarrow> (p \<longrightarrow> r))"
proof
  assume "q \<longrightarrow> r"
  show "(\<not>q \<longrightarrow> \<not>p) \<longrightarrow> (p \<longrightarrow> r)"
  proof
    assume "\<not>q \<longrightarrow> \<not>p"
    show "p \<longrightarrow> r"
    proof
      assume "p"
      hence "\<not>\<not>p" ..
      with `\<not>q \<longrightarrow> \<not>p` have "\<not>\<not>q" by (rule mt)
      hence "q" by (rule notnotD)
      with `q \<longrightarrow> r` show "r" ..
    qed
  qed
qed

-- "La demostración automática es"
lemma ejemplo_11_5:
  "(q \<longrightarrow> r) \<longrightarrow> ((\<not>q \<longrightarrow> \<not>p) \<longrightarrow> (p \<longrightarrow> r))"
by auto

subsection {* Reglas de la disyunción *}

text {*
  Las reglas de la introducción de la disyunción son
  · disjI1: P \<Longrightarrow> P \<or> Q
  · disjI2: Q \<Longrightarrow> P \<or> Q
  La regla de elimación de la disyunción es
  · disjE:  \<lbrakk>P \<or> Q; P \<Longrightarrow> R; Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R 
*}

text {* 
  Ejemplo 12 (p. 11). Demostrar
     p \<or> q \<turnstile> q \<or> p
*}

-- "La demostración detallada es"
lemma ejemplo_12_1:
  assumes "p \<or> q" 
  shows "q \<or> p"
proof -
  have "p \<or> q" using assms by this
  moreover
  { assume 2: "p"
    have "q \<or> p" using 2 by (rule disjI2) }
  moreover
  { assume 3: "q"
    have "q \<or> p" using 3 by (rule disjI1) }
  ultimately show "q \<or> p" by (rule disjE) 
qed    

text {*
  Nota sobre el lenguaje: En la demostración anterior se ha usado
  · "moreover" para separar los bloques y
  · "ultimately" para unir los resultados de los bloques. *}
 
-- "La demostración detallada con reglas implícitas es"
lemma ejemplo_12_2:
  assumes "p \<or> q" 
  shows "q \<or> p"
proof -
  note `p \<or> q`
  moreover
  { assume "p"
    hence "q \<or> p" .. }
  moreover
  { assume "q"
    hence "q \<or> p" .. }
  ultimately show "q \<or> p" ..
qed    

text {*
  Nota sobre el lenguaje: En la demostración anterior se ha usado
  · "note" para copiar un hecho. *}

-- "La demostración hacia atrás es"
lemma ejemplo_12_3:
  assumes 1: "p \<or> q" 
  shows "q \<or> p"
using 1
proof (rule disjE)
  { assume 2: "p"
    show "q \<or> p" using 2 by (rule disjI2) }
next
  { assume 3: "q"
    show "q \<or> p" using 3 by (rule disjI1) }
qed    

-- "La demostración hacia atrás con reglas implícitas es"
lemma ejemplo_12_4:
  assumes "p \<or> q" 
  shows "q \<or> p"
using assms
proof 
  { assume  "p"
    thus "q \<or> p" .. }
next
  { assume "q"
    thus "q \<or> p" .. }
qed    

-- "La demostración automática es"
lemma ejemplo_12_5:
  assumes "p \<or> q" 
  shows "q \<or> p"
using assms
by auto

text {* 
  Ejemplo 13. (p. 12) Demostrar
     q \<longrightarrow> r \<turnstile> p \<or> q \<longrightarrow> p \<or> r
*}

-- "La demostración detallada es" 
lemma ejemplo_13_1:
  assumes 1: "q \<longrightarrow> r"
  shows "p \<or> q \<longrightarrow> p \<or> r"
proof (rule impI)
  assume 2: "p \<or> q"
  thus "p \<or> r"
  proof 
    { assume 3: "p"
      show "p \<or> r" using 3 by (rule disjI1) }
  next
    { assume 4: "q"
      have 5: "r" using 1 4 by (rule mp)
      show "p \<or> r" using 5 by (rule disjI2) }
  qed
qed    

-- "La demostración estructurada es" 
lemma ejemplo_13_2:
  assumes "q \<longrightarrow> r"
  shows "p \<or> q \<longrightarrow> p \<or> r"
proof 
  assume "p \<or> q"
  thus "p \<or> r"
  proof 
    assume "p"
    thus "p \<or> r" .. 
  next
    assume 1:"q"
      have "r" using assms 1 ..
      thus "p \<or> r" .. 
  qed
qed    

-- "La demostración automática es" 
lemma ejemplo_13_3:
  assumes "q \<longrightarrow> r"
  shows "p \<or> q \<longrightarrow> p \<or> r"
using assms
by auto

subsection {* Regla de copia *}

text {* 
  Ejemplo 14 (p. 13). Demostrar
     \<turnstile> p \<longrightarrow> (q \<longrightarrow> p)
*}

-- "La demostración detallada es"
lemma ejemplo_14_1:
  "p \<longrightarrow> (q \<longrightarrow> p)"
proof (rule impI)
  assume 1: "p"
  show "q \<longrightarrow> p" 
  proof (rule impI)
    assume "q"
    show "p" using 1 by this
  qed
qed

-- "La demostración estructurada es"
lemma ejemplo_14_2:
  "p \<longrightarrow> (q \<longrightarrow> p)"
proof 
  assume "p"
  thus "q \<longrightarrow> p" ..
qed

-- "La demostración automática es"
lemma ejemplo_14_3:
  "p \<longrightarrow> (q \<longrightarrow> p)"
by auto

subsection {* Reglas de la negación *}

text {*
  La regla de eliminación de lo falso es
  · FalseE: False \<Longrightarrow> P
  La regla de eliminación de la negación es
  · notE: \<lbrakk>\<not>P; P\<rbrakk> \<Longrightarrow> R
  La regla de introducción de la negación es
  · notI: (P \<Longrightarrow> False) \<Longrightarrow> \<not>P
*}

text {*
  Ejemplo 15 (p. 15). Demostrar
     \<not>p \<or> q \<turnstile> p \<longrightarrow> q
*}

-- "La demostración detallada es"
lemma ejemplo_15_1:
  assumes 1: "\<not>p \<or> q" 
  shows "p \<longrightarrow> q"
proof 
  assume 2: "p"
  note 1
  thus "q"
  proof (* (rule disjE) *)
    assume 3: "\<not>p"
      show "q" using 3 2 by (rule notE) 
   next
    assume 4: "q"
    show "q" using 4 by this
  qed
qed    

-- "La demostración estructurada es"
lemma ejemplo_15_2:
  assumes "\<not>p \<or> q" 
  shows "p \<longrightarrow> q"
proof 
  assume "p"
  note `\<not>p \<or> q`
  thus "q"
  proof
    { assume "\<not>p"
      thus "q" using `p` .. }
  next
    { assume "q"
      thus "q" . }
  qed
qed    

-- "La demostración automática es"
lemma ejemplo_15_3:
  assumes "\<not>p \<or> q" 
  shows "p \<longrightarrow> q"
using assms
by auto

text {* 
  Ejemplo 16 (p. 16). Demostrar
     p \<longrightarrow> q, p \<longrightarrow> \<not>q \<turnstile> \<not>p
*}

-- "La demostración detallada es"
lemma ejemplo_16_1:
  assumes 1: "p \<longrightarrow> q" and 
          2: "p \<longrightarrow> \<not>q" 
  shows "\<not>p"    
proof (rule notI)
  assume 3: "p"
  have 4: "q" using 1 3 by (rule mp)
  have 5: "\<not>q" using 2 3 by (rule mp)
  show False using 5 4 by (rule notE)
qed

-- "La demostración estructurada es"
lemma ejemplo_16_2:
  assumes "p \<longrightarrow> q"
          "p \<longrightarrow> \<not>q" 
  shows "\<not>p"    
proof 
  assume "p"
  have "q" using assms(1) `p` ..
  have "\<not>q" using assms(2) `p` ..
  thus False using `q` ..
qed

-- "La demostración automática es"
lemma ejemplo_16_3:
  assumes "p \<longrightarrow> q"
          "p \<longrightarrow> \<not>q" 
  shows "\<not>p"    
using assms
by auto

subsection {* Reglas del bicondicional *}

text {*
  La regla de introducción del bicondicional es
  · iffI: \<lbrakk>P \<Longrightarrow> Q; Q \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P \<longleftrightarrow> Q
  Las reglas de eliminación del bicondicional son
  · iffD1: \<lbrakk>Q \<longleftrightarrow> P; Q\<rbrakk> \<Longrightarrow> P 
  · iffD2: \<lbrakk>P \<longleftrightarrow> Q; Q\<rbrakk> \<Longrightarrow> P
*}

text {* 
  Ejemplo 17 (p. 17) Demostrar
*}

-- "La demostración detallada es"
lemma ejemplo_17_1:
  "(p \<and> q) \<longleftrightarrow> (q \<and> p)"
proof (rule iffI)
  { assume 1: "p \<and> q"
    have 2: "p" using 1 by (rule conjunct1)
    have 3: "q" using 1 by (rule conjunct2)
    show "q \<and> p" using 3 2 by (rule conjI) }
next
  { assume 4: "q \<and> p"
    have 5: "q" using 4 by (rule conjunct1)
    have 6: "p" using 4 by (rule conjunct2)
    show "p \<and> q" using 6 5 by (rule conjI) }
qed

-- "La demostración estructurada es"
lemma ejemplo_17_2:
  "(p \<and> q) \<longleftrightarrow> (q \<and> p)"
proof 
  { assume 1: "p \<and> q"
    have "p" using 1 ..
    have "q" using 1 ..
    show "q \<and> p" using `q` `p` .. }
next
  { assume 2: "q \<and> p"
    have "q" using 2 ..
    have "p" using 2 ..
    show "p \<and> q" using `p` `q`  .. }
qed

-- "La demostración automática es"
lemma ejemplo_17_3:
  "(p \<and> q) \<longleftrightarrow> (q \<and> p)"
by auto

text {*
  Ejemplo 18 (p. 18). Demostrar
     p \<longleftrightarrow> q, p \<or> q \<turnstile> p \<and> q
*}

-- "La demostración detallada es"
lemma ejemplo_18_1:
  assumes 1: "p \<longleftrightarrow> q" and 
          2: "p \<or> q"  
  shows "p \<and> q"
using 2
proof (rule disjE)
  { assume 3: "p"
    have 4: "q" using 1 3 by (rule iffD1)
    show "p \<and> q" using 3 4 by (rule conjI) }
next
  { assume 5: "q"
    have 6: "p" using 1 5 by (rule iffD2)
    show "p \<and> q" using 6 5 by (rule conjI) }
qed

-- "La demostración estructurada es"
lemma ejemplo_18_2:
  assumes "p \<longleftrightarrow> q"
          "p \<or> q"  
  shows  "p \<and> q"
using assms(2)
proof
  { assume "p"
    with assms(1) have "q" ..
    with `p` show "p \<and> q" .. }
next
  { assume "q"
    with assms(1) have "p" ..
    thus "p \<and> q" using `q` .. }
qed

-- "La demostración automática es"
lemma ejemplo_18_3:
  assumes "p \<longleftrightarrow> q"
          "p \<or> q"  
  shows "p \<and> q"
using assms
by auto

subsection {* Reglas derivadas *}

subsubsection {* Regla del modus tollens *}

text {* 
  Ejemplo 19 (p. 20) Demostrar la regla del modus tollens a partir de
  las reglas básicas. 
*}

-- "La demostración detallada es"
lemma ejemplo_20_1:
  assumes 1: "F \<longrightarrow> G" and 
          2: "\<not>G" 
  shows "\<not>F"
proof (rule notI)
  assume 3: "F"
  have 4: "G" using 1 3 by (rule mp)
  show False using 2 4 by (rule notE)
qed    

-- "La demostración estructurada es"
lemma ejemplo_20_2:
  assumes "F \<longrightarrow> G"
          "\<not>G" 
  shows   "\<not>F"
proof 
  assume "F"
  with assms(1) have "G" ..
  with assms(2) show False ..
qed    

-- "La demostración automática es"
lemma ejemplo_20_3:
  assumes "F \<longrightarrow> G"
          "\<not>G" 
  shows "\<not>F"
using assms
by auto

subsubsection {* Regla de la introducción de la doble negación *}

text {*
  Ejemplo 21 (p. 21) Demostrar la regla de introducción de la doble
  negación a partir de las reglas básicas.
*}

-- "La demostración detallada es"
lemma ejemplo_21_1:
  assumes 1: "F" 
  shows "\<not>\<not>F"
proof (rule notI)
  assume 2: "\<not>F"
  show False using 2 1 by (rule notE)
qed    

-- "La demostración estructurada es"
lemma ejemplo_21_2:
  assumes "F" 
  shows "\<not>\<not>F"
proof 
  assume "\<not>F"
  thus False using assms ..
qed    

-- "La demostración automática es"
lemma ejemplo_21_3:
  assumes "F" 
  shows "\<not>\<not>F"
using assms
by auto

subsubsection {* Regla de reducción al absurdo *}

text {*
  La regla de reducción al absurdo en Isabelle se correponde con la
  regla clásica de contradicción 
  · ccontr: (\<not>P \<Longrightarrow> False) \<Longrightarrow> P
*}

subsubsection {* Ley del tercio excluso *}

text {*
  La ley del tercio excluso es 
  · excluded_middle: \<not>P \<or> P
*}

text {*
  Ejemplo 22 (p. 23). Demostrar la ley del tercio excluso a partir de
  las reglas básicas.  
*}

-- "La demostración detallada es"
lemma ejemplo_22_1:
  "F \<or> \<not>F"
proof (rule ccontr)
  assume 1: "\<not>(F \<or> \<not>F)"
  thus False
  proof (rule notE)
    show "F \<or> \<not>F"
    proof (rule disjI2)
      show "\<not>F"
      proof (rule notI)
        assume 2: "F"
        hence 3: "F \<or> \<not>F" by (rule disjI1)
        show False using 1 3 by (rule notE)
      qed
    qed
  qed
qed
    
-- "La demostración estructurada es"
lemma ejemplo_22_2:
  "F \<or> \<not>F"
proof (rule ccontr)
  assume "\<not>(F \<or> \<not>F)"
  thus False
  proof (rule notE)
    show "F \<or> \<not>F"
    proof (rule disjI2)
      show "\<not>F"
      proof (rule notI)
        assume "F"
        hence "F \<or> \<not>F" ..
        with `\<not>(F \<or> \<not>F)`show False ..
      qed
    qed
  qed
qed
    
-- "La demostración automática es"
lemma ejemplo_22_3:
  "F \<or> \<not>F"
using assms
by auto

text {* 
  Ejemplo 23 (p. 24). Demostrar
     p \<longrightarrow> q \<turnstile> \<not>p \<or> q
*}

-- "La demostración detallada es"
lemma ejemplo_23_1:
  assumes 1: "p \<longrightarrow> q" 
  shows "\<not>p \<or> q"
proof -
  have "\<not>p \<or> p" by (rule excluded_middle)
  thus "\<not>p \<or> q"
  proof (rule disjE)
    { assume "\<not>p"
      thus "\<not>p \<or> q" by (rule disjI1) }
  next
    { assume 2: "p"
      have "q" using 1 2 by (rule mp)
      thus "\<not>p \<or> q" by (rule disjI2) }
  qed
qed    

-- "La demostración estructurada es"
lemma ejemplo_23_2:
  assumes "p \<longrightarrow> q" 
  shows "\<not>p \<or> q"
proof -
  have "\<not>p \<or> p" ..
  thus "\<not>p \<or> q"
  proof 
    { assume "\<not>p"
      thus "\<not>p \<or> q" .. }
  next
    { assume "p"
      with assms have "q" ..
      thus "\<not>p \<or> q" .. }
  qed
qed    

-- "La demostración automática es"
lemma ejemplo_23_3:
  assumes "p \<longrightarrow> q" 
  shows "\<not>p \<or> q"
using assms
by auto

subsection {* Demostraciones por contradicción *}

text {* 
  Ejemplo 24. Demostrar que 
     \<not>p, p \<or> q \<turnstile> q
*}

-- "La demostración detallada es"
lemma ejemplo_24_1:
  assumes "\<not>p"
          "p \<or> q"
  shows   "q"
using `p \<or> q`
proof (rule disjE)
  assume "p"
  with assms(1) show "q" by contradiction 
next
  assume "q"
  thus "q" by assumption
qed

-- "La demostración estructurada es"
lemma ejemplo_24_2:
  assumes "\<not>p"
          "p \<or> q"
  shows "q"
using `p \<or> q`
proof 
  assume "p"
  with assms(1) show "q" ..
next
  assume "q"
  thus "q" .
qed

-- "La demostración automática es"
lemma ejemplo_24_3:
  assumes "\<not>p"
          "p \<or> q"
  shows "q"
using assms
by auto

end
