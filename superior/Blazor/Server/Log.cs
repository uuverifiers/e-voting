// Formally verified E-Voting using Dafny
// Copyright (C) 2025 Authors Superior Group
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as
// published by the Free Software Foundation, either version 3 of the
// License, or (at your option) any later version.
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
// See the GNU Affero General Public License for more details.
// You should have received a copy of the GNU Affero General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace E_Voting
{
    public static class Log
    {
        private static readonly object logLock = new object();
        private const string logFile = "../log.txt";

        public static void Clear()
        {
            lock (logLock)
            {
                if (!File.Exists(logFile))
                {
                    return;
                }

                try
                {
                    string[] lines = File.ReadAllLines(logFile);
                    DateTime threshold = DateTime.UtcNow.AddDays(-Config.LogCleanerThreshold);

                    List<string> keptLines = new List<string>();
                    for(int i = 0; i < lines.Length - 2; i++)
                    {
                        if (DateTime.TryParse(lines[i], out DateTime timestamp))
                        {
                            if (timestamp >= threshold)
                            {
                                keptLines.Add(lines[i]);
                                keptLines.Add(lines[i + 1]);
                                keptLines.Add(lines[i + 2]);
                                i += 2;
                            }
                        }
                        else
                        {
                            WriteError("Bad format found in log!");
                            return;
                        }
                    }

                    File.WriteAllLines(logFile, keptLines);
                }
                catch (Exception e)
                {
                    WriteError("Failed to clear old logs: " + e.Message);
                }
            }
        }

        public static void Write(string text)
        {
            lock(logLock)
            {
                ConsoleColor current = Console.ForegroundColor;
                Console.ForegroundColor = ConsoleColor.White;
                Console.WriteLine(DateTime.UtcNow);
                Console.ForegroundColor = current;

                string logText = text + " - [" + Thread.CurrentThread.ManagedThreadId + "]" + Environment.NewLine;
                Console.WriteLine(logText);
                Console.ForegroundColor = ConsoleColor.White;

                if (Config.EnableLogging)
                {
                    try
                    {
                        File.AppendAllText(logFile, DateTime.UtcNow + Environment.NewLine + logText + Environment.NewLine);
                        Trim(logFile, 10000);
                    }
                    catch (Exception e)
                    {
                        Console.ForegroundColor = ConsoleColor.Red;
                        Console.WriteLine("Failed to write to log.txt: " + e.Message);
                        Console.ForegroundColor = ConsoleColor.White;
                    }
                }
            }
        }

        private static void Trim(string file, int maxLines)
        {
            string[] lines = File.ReadAllLines(file);
            if (lines.Length <= maxLines)
            {
                return;
            }

            // remove oldest lines to keep only maxLines lines at the end
            int linesToRemove = lines.Length - maxLines;
            string[] trimmedLines = lines.Skip(linesToRemove).ToArray();

            File.WriteAllLines(file, trimmedLines);
        }

        public static void WriteError(string text)
        {
            lock(logLock)
            {
                Console.ForegroundColor = ConsoleColor.Red;
                Write(text);
            }
        }

        public static void WriteSuccess(string text)
        {
            lock(logLock)
            {
                Console.ForegroundColor = ConsoleColor.Green;
                Write(text);
            }
        }

        public static void WriteWarning(string text)
        {
            lock(logLock)
            {
                Console.ForegroundColor = ConsoleColor.Yellow;
                Write(text);
            }
        }
    }
}
