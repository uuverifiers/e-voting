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

using System.Security.Cryptography;

namespace E_Voting
{
    public static class RandomHelper
    {
        private static readonly char[] values = {
            'a','b','c','d','e','f','g','h','i','j','k','l','m',
            'n','o','p','q','r','s','t','u','v','w','x','y','z',

            'A','B','C','D','E','F','G','H','I','J','K','L','M',
            'N','O','P','Q','R','S','T','U','V','W','X','Y','Z'
        };

        public static string GetToken(int length)
        {
            string result = "";
            for(int i = 0; i < length; i++)
            {
                result += GetRandomChar();
            }

            return result;
        }

        private static char GetRandomChar()
        {
            // get random number (unpredictable)
            byte[] buffer = new byte[4];
            RandomNumberGenerator.Fill(buffer);

            // ensure it is positive
            int index = BitConverter.ToInt32(buffer, 0);
            if(index < 0) 
            { 
                index = index * -1;
            }

            // get a number between 0 and values.Length - 1 (modulo)
            return values[index % values.Length];
        }
    }
}
