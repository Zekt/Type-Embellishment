{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}

import Control.Applicative
import Control.Monad
import Control.Monad.Except

import qualified Data.List as List
import qualified Data.List.NonEmpty as List1
import Data.List.NonEmpty ( pattern (:|) )
import Data.Maybe

import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.FilePath.Find
import System.IO
import System.FilePath (takeDirectory)

allOutputFile  = "Everything"
safeOutputFile = "EverythingSafe"
srcDir         = "src"

---------------------------------------------------------------------------
-- Files with a special status

-- | Checks whether a module is declared (un)safe

unsafeModules :: [FilePath]
unsafeModules = map modToFile
  []

isUnsafeModule :: FilePath -> Bool
isUnsafeModule fp =
    unqualifiedModuleName fp == "Unsafe"
    || fp `elem` unsafeModules

-- | Checks whether a module is declared as using K

withKModules :: [FilePath]
withKModules = map modToFile
  [ "Generics.SimpleContainer"
  , "Generics.SimpleContainer.All"
  , "Generics.SimpleContainer.Any"
  , "Generics.Ornament"
  , "Generics.Ornament.Algebraic"
  , "Generics.Ornament.Algebraic.Isomorphism"
  , "Generics.Ornament.Description"
  , "Examples.WithMacros.List"
  , "Examples.WithMacros.STLC"
  , "Examples.WithMacros.BST"
  , "Examples.WithMacros.Acc"
  , "Examples.WithMacros.W"
  , "Examples.WithoutMacros.List"
  , "Examples.WithoutMacros.STLC"
  , "Examples.WithoutMacros.BST"
  , "Examples.WithoutMacros.Acc"
  , "Examples.WithoutMacros.W"
  ]

isWithKModule :: FilePath -> Bool
isWithKModule =
  -- GA 2019-02-24: it is crucial to use an anonymous lambda
  -- here so that `withKModules` is shared between all calls
  -- to `isWithKModule`.
  \ fp -> unqualifiedModuleName fp == "WithK"
       || fp `elem` withKModules

sizedTypesModules :: [FilePath]
sizedTypesModules = map modToFile
  []

isSizedTypesModule :: FilePath -> Bool
isSizedTypesModule =
  \ fp -> fp `elem` sizedTypesModules

unqualifiedModuleName :: FilePath -> String
unqualifiedModuleName = dropExtension . takeFileName

-- | Returns 'True' for all Agda files except for core modules.

isLibraryModule :: FilePath -> Bool
isLibraryModule f =
  takeExtension f `elem` [".agda", ".lagda"]
  && unqualifiedModuleName f /= "Core"

isExcludedModule :: FilePath -> Bool
isExcludedModule f = takeDirectory f == srcDir </> "Tests"

---------------------------------------------------------------------------
-- Analysing library files

type Exc = Except String

-- | A crude classifier looking for lines containing options

data Status = Deprecated | Unsafe | Safe
  deriving (Eq)

classify :: FilePath -> [String] -> Exc Status
classify fp ls
  -- We start with sanity checks
  | isUnsafe && safe          = throwError $ fp ++ contradiction "unsafe" "safe"
  | not (isUnsafe || safe)    = throwError $ fp ++ uncategorized "unsafe" "safe"
  | isWithK && withoutK       = throwError $ fp ++ contradiction "as relying on K" "without-K"
  | isWithK && not withK      = throwError $ fp ++ missingWithK
  | not (isWithK || withoutK) = throwError $ fp ++ uncategorized "as relying on K" "without-K"
  -- And then perform the actual classification
  | isUnsafe                  = pure $ Unsafe
  | safe                      = pure $ Safe
  -- We know that @not (isUnsafe || safe)@, all cases are covered
  | otherwise                 = error "IMPOSSIBLE"

  where

    -- based on declarations
    isWithK  = isWithKModule fp
    isUnsafe = isUnsafeModule fp

    -- based on detected OPTIONS
    safe        = option "--safe"
    withK       = option "--with-K"
    withoutK    = option "--without-K"

    -- GA 2019-02-24: note that we do not reprocess the whole module for every
    -- option check: the shared @options@ definition ensures we only inspect a
    -- handful of lines (at most one, ideally)
    option str = let detect = List.isSubsequenceOf ["{-#", "OPTIONS", str, "#-}"]
                  in any detect options
    options    = words <$> filter (List.isInfixOf "OPTIONS") ls

    -- formatting error messages
    contradiction d o = unwords
      [ " is declared", d, "but uses the", "--" ++ o, "option." ]
    uncategorized d o = unwords
      [ " is not declared", d, "but not using the", "--" ++ o, "option either." ]

    missingWithK = " is declared as relying on K but not using the --with-K option."

data LibraryFile = LibraryFile
  { filepath   :: FilePath -- ^ FilePath of the source file
  , status     :: Status   -- ^ Safety options used by the module
  }

analyse :: FilePath -> IO LibraryFile
analyse fp = do
  ls <- lines <$> readFileUTF8 fp
  cl <- runExc $ classify fp ls
  return $ LibraryFile
    { filepath   = fp
    , status     = cl
    }

checkFilePaths :: String -> [FilePath] -> IO ()
checkFilePaths cat fps = forM_ fps $ \ fp -> do
  b <- doesFileExist fp
  unless b $
    die $ fp ++ " is listed as " ++ cat ++ " but does not exist."

---------------------------------------------------------------------------
-- Collecting all non-Core library files, analysing them and generating
-- 4 files:
-- Everything.agda                 all the modules
-- EverythingSafe.agda             all the safe modules

main = do
  args <- getArgs
  case args of
    [] -> return ()
    _  -> hPutStr stderr usage >> exitFailure

  checkFilePaths "unsafe" unsafeModules
  checkFilePaths "using K" withKModules

  modules <- filter (not . isExcludedModule) . filter isLibraryModule . List.sort <$>
               find always
                    (extension ==? ".agda" ||? extension ==? ".lagda")
                    srcDir
  libraryfiles <- filter ((Deprecated /=) . status) <$> mapM analyse modules

  let mkModule str = "module " ++ str ++ " where"

  writeFileUTF8 (allOutputFile ++ ".agda") $
    unlines [ "{-# OPTIONS --rewriting --guardedness --sized-types #-}\n"
            , "-- !!! THIS MODULE IS NOT SUPPOSED TO BE CHECKED DIRECTLY !!! ---"
            , mkModule allOutputFile
            , format libraryfiles
            ]

  writeFileUTF8 (safeOutputFile ++ ".agda") $
    unlines [ "{-# OPTIONS --safe --guardedness #-}\n"
            , "-- !!! THIS MODULE IS NOT SUPPOSED TO BE CHECKED DIRECTLY !!! ---"
            , mkModule safeOutputFile
            , format $ filter ((Unsafe /=) . status) libraryfiles
            ]

-- | Usage info.

usage :: String
usage = unlines
  [ "GenerateEverything: A utility program for Agda's standard library."
  , ""
  , "Usage: GenerateEverything"
  , ""
  , "This program should be run in the base directory of a clean checkout of"
  , "the library."
  , ""
  , "The program generates documentation for the library by extracting"
  , "headers from library modules. The output is written to " ++ allOutputFile
  ]


-- | Formats the extracted module information.

format :: [LibraryFile] -> String
format = unlines . concatMap fmt
  where
  fmt lf = ["import " ++ fileToMod (filepath lf)]

-- | Translates back and forth between a file name and the corresponding module
--   name. We assume that the file name corresponds to an Agda module under
--   'srcDir'.

fileToMod :: FilePath -> String
fileToMod = map slashToDot . dropExtension . makeRelative srcDir
  where
  slashToDot c | isPathSeparator c = '.'
               | otherwise         = c

modToFile :: String -> FilePath
modToFile name = concat [ srcDir, [pathSeparator], map dotToSlash name, ".agda" ]
  where
  dotToSlash c | c == '.'  = pathSeparator
               | otherwise = c

-- | A variant of 'readFile' which uses the 'utf8' encoding.

readFileUTF8 :: FilePath -> IO String
readFileUTF8 f = do
  h <- openFile f ReadMode
  hSetEncoding h utf8
  s <- hGetContents h
  length s `seq` return s

-- | A variant of 'writeFile' which uses the 'utf8' encoding.

writeFileUTF8 :: FilePath -> String -> IO ()
writeFileUTF8 f s = withFile f WriteMode $ \h -> do
  hSetEncoding h utf8
  hPutStr h s

-- | Turning exceptions into fatal errors.

runExc :: Exc a -> IO a
runExc = either die return . runExcept
