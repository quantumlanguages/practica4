{--
Practica 3
El lenguaje MiniHS (EAB extendido con cáculo lambda). Semátnica
Autores:
Edgar Quiroz Castañeda
Sandra del Mar Soto Corderi
--}

module BAE.Semantic (
  Type(..),
  evale, eval
) where
  
  import BAE.Dynamic
  import BAE.Type
  
